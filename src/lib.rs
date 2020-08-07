// Copyright 2020 CoD Technologies Corp.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Translate from PostgreSQL's like implementation.
// See `like.c` and `like_match.c` in PostgreSQL's source code.

//! A SQL `like` style pattern matching.

use std::error::Error;
use std::fmt::{self, Display};

/// SQL `like` style pattern matching.
///
/// If `pattern` does not contain `%` or `_`, then the pattern only represents the `pattern` itself;
/// in that case `like` acts like the equals operator.
/// An underscore (`_`) in pattern stands for (matches) any single character;
/// a percent sign (`%`) matches any sequence of zero or more characters.
pub trait Like {
    /// The associated error which can be returned from pattern matching.
    type Err;

    /// Check if `self` match a pattern.
    ///
    /// Returns `true` if `self` matches the supplied `pattern`.
    fn like(&self, pattern: &Self) -> Result<bool, Self::Err>;

    /// Check if `self`  match a pattern.
    ///
    /// Returns `true` if `self` doesn't match the supplied `pattern`.
    #[inline]
    fn not_like(&self, pattern: &Self) -> Result<bool, Self::Err> {
        self.like(pattern).map(|m| !m)
    }
}

trait Traverser {
    fn len(&self) -> usize;
    fn next_char(&mut self);
    fn next_byte(&mut self);
    fn raw_char(&self) -> u8;
    fn char(&self) -> u8;
    fn char_at(&self, index: usize) -> u8;
}

#[derive(PartialEq, Copy, Clone)]
enum Matched {
    True,
    False,
    Abort,
}

fn like<T: Traverser>(input: &mut T, pattern: &mut T) -> Result<Matched, InvalidPatternError> {
    // Fast path for match-everything pattern
    if pattern.len() == 1 && pattern.raw_char() == b'%' {
        return Ok(Matched::True);
    }

    // In this loop, we advance by char when matching wildcards (and thus on
    // recursive entry to this function we are properly char-synced). On other
    // occasions it is safe to advance by byte, as the text and pattern will
    // be in lockstep. This allows us to perform all comparisons between the
    // text and pattern on a byte by byte basis, even for multi-byte
    // encodings.
    while input.len() > 0 && pattern.len() > 0 {
        if pattern.raw_char() == b'\\' {
            // Next pattern byte must match literally, whatever it is
            pattern.next_byte();
            // ... and there had better be one, per SQL standard
            if pattern.len() <= 0 {
                return Err(InvalidPatternError);
            }

            if input.char() != pattern.char() {
                return Ok(Matched::False);
            }
        } else if pattern.raw_char() == b'%' {
            // % processing is essentially a search for a text position at
            // which the remainder of the text matches the remainder of the
            // pattern, using a recursive call to check each potential match.
            //
            // If there are wildcards immediately following the %, we can skip
            // over them first, using the idea that any sequence of N _'s and
            // one or more %'s is equivalent to N _'s and one % (ie, it will
            // match any sequence of at least N text characters).  In this way
            // we will always run the recursive search loop using a pattern
            // fragment that begins with a literal character-to-match, thereby
            // not recursing more than we have to.
            pattern.next_byte();

            while pattern.len() > 0 {
                let pattern_raw_char = pattern.raw_char();
                if pattern_raw_char == b'%' {
                    pattern.next_byte();
                } else if pattern_raw_char == b'_' {
                    // If not enough text left to match the pattern, ABORT
                    if input.len() <= 0 {
                        return Ok(Matched::Abort);
                    }
                    input.next_char();
                    pattern.next_byte();
                } else {
                    break; // Reached a non-wildcard pattern char
                }
            }

            // If we're at end of pattern, match: we have a trailing % which
            // matches any remaining text string.
            if pattern.len() <= 0 {
                return Ok(Matched::True);
            }

            // Otherwise, scan for a text position at which we can match the
            // rest of the pattern.  The first remaining pattern char is known
            // to be a regular or escaped literal character, so we can compare
            // the first pattern byte to each text byte to avoid recursing
            // more than we have to.  This fact also guarantees that we don't
            // have to consider a match to the zero-length substring at the
            // end of the text.
            let first_pat = if pattern.raw_char() == b'\\' {
                if pattern.len() < 2 {
                    return Err(InvalidPatternError);
                }
                pattern.char_at(1)
            } else {
                pattern.char()
            };

            while input.len() > 0 {
                if input.char() == first_pat {
                    let matched = like(input, pattern)?;
                    if matched != Matched::False {
                        return Ok(matched); // True or Abort
                    }
                }

                input.next_char();
            }

            // End of text with no match, so no point in trying later places
            // to start matching this pattern.
            return Ok(Matched::Abort);
        } else if pattern.raw_char() == b'_' {
            // _ matches any single character, and we know there is one
            input.next_char();
            pattern.next_byte();
            continue;
        } else if pattern.char() != input.char() {
            // non-wildcard pattern char fails to match text char
            return Ok(Matched::False);
        }

        // Pattern and text match, so advance.
        //
        // It is safe to use NextByte instead of NextChar here, even for
        // multi-byte character sets, because we are not following immediately
        // after a wildcard character. If we are in the middle of a multibyte
        // character, we must already have matched at least one byte of the
        // character from both text and pattern; so we cannot get out-of-sync
        // on character boundaries.  And we know that no backend-legal
        // encoding allows ASCII characters such as '%' to appear as non-first
        // bytes of characters, so we won't mistakenly detect a new wildcard.
        input.next_byte();
        pattern.next_byte();
    }

    if input.len() > 0 {
        return Ok(Matched::False); // end of pattern, but not of text
    }

    // End of text, but perhaps not of pattern.  Match iff the remaining
    // pattern can match a zero-length string, ie, it's zero or more %'s.
    while pattern.len() > 0 && pattern.raw_char() == b'%' {
        pattern.next_byte();
    }
    if pattern.len() <= 0 {
        return Ok(Matched::True);
    }

    // End of text with no match, so no point in trying later places to start
    // matching this pattern.
    return Ok(Matched::Abort);
}

/// Errors which can occur when attempting to match a pattern.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct InvalidPatternError;

impl Display for InvalidPatternError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid pattern")
    }
}

impl Error for InvalidPatternError {}

struct StrTraverser<'a> {
    bytes: &'a [u8],
}

impl<'a> StrTraverser<'a> {
    #[inline]
    const fn new(s: &'a str) -> Self {
        Self {
            bytes: s.as_bytes(),
        }
    }
}

impl<'a> Traverser for StrTraverser<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.bytes.len()
    }

    #[inline]
    fn next_char(&mut self) {
        self.next_byte();
        while self.bytes.len() > 0 && (self.raw_char() & 0xC0) == 0x80 {
            self.next_byte();
        }
    }

    #[inline]
    fn next_byte(&mut self) {
        self.bytes = &self.bytes[1..];
    }

    #[inline]
    fn raw_char(&self) -> u8 {
        self.bytes[0]
    }

    #[inline]
    fn char(&self) -> u8 {
        self.char_at(0)
    }

    #[inline]
    fn char_at(&self, index: usize) -> u8 {
        self.bytes[index]
    }
}

struct BytesTraverser<'a> {
    bytes: &'a [u8],
}

impl<'a> BytesTraverser<'a> {
    #[inline]
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }
}

impl<'a> Traverser for BytesTraverser<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.bytes.len()
    }

    #[inline]
    fn next_char(&mut self) {
        self.next_byte()
    }

    #[inline]
    fn next_byte(&mut self) {
        self.bytes = &self.bytes[1..];
    }

    #[inline]
    fn raw_char(&self) -> u8 {
        self.bytes[0]
    }

    #[inline]
    fn char(&self) -> u8 {
        self.char_at(0)
    }

    #[inline]
    fn char_at(&self, index: usize) -> u8 {
        self.bytes[index]
    }
}

impl Like for str {
    type Err = InvalidPatternError;

    #[inline]
    fn like(&self, pattern: &Self) -> Result<bool, Self::Err> {
        let mut input = StrTraverser::new(self);
        let mut pattern = StrTraverser::new(pattern);
        let result = like(&mut input, &mut pattern)?;
        Ok(matches!(result, Matched::True))
    }
}

impl Like for [u8] {
    type Err = InvalidPatternError;

    #[inline]
    fn like(&self, pattern: &Self) -> Result<bool, Self::Err> {
        let mut input = BytesTraverser::new(self);
        let mut pattern = BytesTraverser::new(pattern);
        let result = like(&mut input, &mut pattern)?;
        Ok(matches!(result, Matched::True))
    }
}

#[cfg(test)]
mod tests {
    use crate::Like;

    #[test]
    fn test_like_str() {
        assert!("hello我的world".like("%").unwrap());
        assert!("hello我的world".like("he%world").unwrap());
        assert!("hello我的world".like("%我%").unwrap());
        assert!("hello我的world".like("he%d").unwrap());
        assert!("hello我的world".like("h%我_%").unwrap());
    }

    #[test]
    fn test_like_bytes() {
        assert!(b"hello".like(b"%").unwrap());
        assert!(b"hello".like(b"he%").unwrap());
        assert!(b"hello".like(b"%llo").unwrap());
        assert!(b"hello".like(b"he%o").unwrap());
        assert!(b"hello".like(b"h_l%o").unwrap());
    }
}
