// Copyright 2020-2021 CoD Technologies Corp.
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
//!
//! ## Usage
//!
//! To do a patten matching, use `Like`:
//!
//! ```
//! use like::Like;
//!
//! assert!(Like::<false>::like("Hello, world!", "Hello%").unwrap());
//! ```
//!
//! To do a case-insensitive pattern matching, use `ILike`:
//!
//! ```
//! use like::ILike;
//!
//! assert!(ILike::<false>::ilike("Hello, world!", "HELLO%").unwrap());
//! ```
//!
//! To convert the pattern to use standard backslash escape convention, use `Escape`:
//!
//! ```
//! use like::Escape;
//!
//! assert_eq!("Hello$%".escape("$").unwrap(), "Hello\\%");
//! ```

use std::error::Error;
use std::fmt::{self, Display};

/// SQL `like` style pattern matching.
///
/// If `pattern` does not contain `%` or `_`, then the pattern only represents the `pattern` itself;
/// in that case `like` acts like the equals operator.
/// An underscore (`_`) in pattern stands for (matches) any single character;
/// a percent sign (`%`) matches any sequence of zero or more characters.
pub trait Like<const HAS_ESCAPE: bool> {
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

/// SQL `ilike` style pattern matching.
///
/// `ilike` is a case-insensitive version of `like` style pattern matching;
/// make the input and pattern to be lowercase and do comparison.
/// Other internal implementation are the same as `like`.
pub trait ILike<const HAS_ESCAPE: bool> {
    /// The associated error which can be returned from pattern matching.
    type Err;

    /// Check if `self` match a pattern.
    ///
    /// Returns `true` if `self` matches the supplied `pattern`.
    fn ilike(&self, pattern: &Self) -> Result<bool, Self::Err>;

    /// Check if `self`  match a pattern.
    ///
    /// Returns `true` if `self` doesn't match the supplied `pattern`.
    #[inline]
    fn not_ilike(&self, pattern: &Self) -> Result<bool, Self::Err> {
        self.ilike(pattern).map(|m| !m)
    }
}

/// Convert the pattern to use standard backslash escape convention.
pub trait Escape {
    /// The associated error which can be returned from pattern matching.
    type Err;
    /// The output type of conversion.
    type Output;

    /// Change if `self`  have a escape character.
    ///
    /// Returns new pattern if there are any escape characters in the pattern.
    fn escape(&self, esc: &Self) -> Result<Self::Output, Self::Err>;
}

trait Traverser {
    fn len(&self) -> usize;

    fn advance_byte(&mut self);

    #[inline]
    fn advance_char(&mut self) {
        self.advance_byte()
    }

    fn raw_byte_at(&self, index: usize) -> u8;

    #[inline]
    fn next_raw_byte(&self) -> u8 {
        self.raw_byte_at(0)
    }

    #[inline]
    fn byte_at(&self, index: usize) -> u8 {
        self.raw_byte_at(index)
    }

    #[inline]
    fn next_byte(&self) -> u8 {
        self.byte_at(0)
    }

    #[inline]
    fn next_raw_char(&self) -> char {
        self.next_raw_byte() as char
    }
}

#[derive(PartialEq, Copy, Clone)]
enum Matched {
    True,
    False,
    Abort,
}

/// Errors which can occur when attempting to match a pattern.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct InvalidPatternError;

impl Display for InvalidPatternError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "missing or illegal character following the escape character"
        )
    }
}

impl Error for InvalidPatternError {}

fn like<T, const HAS_ESCAPE: bool>(
    input: &mut T,
    pattern: &mut T,
) -> Result<Matched, InvalidPatternError>
where
    T: Traverser + Clone,
{
    // Fast path for match-everything pattern
    if pattern.len() == 1 && pattern.next_raw_byte() == b'%' {
        return Ok(Matched::True);
    }

    // In this loop, we advance by char when matching wildcards (and thus on
    // recursive entry to this function we are properly char-synced). On other
    // occasions it is safe to advance by byte, as the text and pattern will
    // be in lockstep. This allows us to perform all comparisons between the
    // text and pattern on a byte by byte basis, even for multi-byte
    // encodings.
    while input.len() > 0 && pattern.len() > 0 {
        if HAS_ESCAPE && pattern.next_raw_byte() == b'\\' {
            // Next pattern byte must match literally, whatever it is
            pattern.advance_byte();
            // ... and there had better be one, per SQL standard
            if pattern.len() == 0 {
                return Err(InvalidPatternError);
            }

            if input.next_byte() != pattern.next_byte() {
                return Ok(Matched::False);
            }
        } else if pattern.next_raw_byte() == b'%' {
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
            pattern.advance_byte();

            while pattern.len() > 0 {
                let pattern_raw_char = pattern.next_raw_byte();
                if pattern_raw_char == b'%' {
                    pattern.advance_byte();
                } else if pattern_raw_char == b'_' {
                    // If not enough text left to match the pattern, ABORT
                    if input.len() == 0 {
                        return Ok(Matched::Abort);
                    }
                    input.advance_char();
                    pattern.advance_byte();
                } else {
                    break; // Reached a non-wildcard pattern char
                }
            }

            // If we're at end of pattern, match: we have a trailing % which
            // matches any remaining text string.
            if pattern.len() == 0 {
                return Ok(Matched::True);
            }

            // Otherwise, scan for a text position at which we can match the
            // rest of the pattern.  The first remaining pattern char is known
            // to be a regular or escaped literal character, so we can compare
            // the first pattern byte to each text byte to avoid recursing
            // more than we have to.  This fact also guarantees that we don't
            // have to consider a match to the zero-length substring at the
            // end of the text.
            let first_pat = if HAS_ESCAPE && pattern.next_raw_byte() == b'\\' {
                if pattern.len() < 2 {
                    return Err(InvalidPatternError);
                }
                pattern.byte_at(1)
            } else {
                pattern.next_byte()
            };

            while input.len() > 0 {
                if input.next_byte() == first_pat {
                    let mut i = input.clone();
                    let mut p = pattern.clone();
                    let matched = like::<T, HAS_ESCAPE>(&mut i, &mut p)?;
                    if matched != Matched::False {
                        return Ok(matched); // True or Abort
                    }
                }

                input.advance_char();
            }

            // End of text with no match, so no point in trying later places
            // to start matching this pattern.
            return Ok(Matched::Abort);
        } else if pattern.next_raw_byte() == b'_' {
            // _ matches any single character, and we know there is one
            input.advance_char();
            pattern.advance_byte();
            continue;
        } else if pattern.next_byte() != input.next_byte() {
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
        input.advance_byte();
        pattern.advance_byte();
    }

    if input.len() > 0 {
        return Ok(Matched::False); // end of pattern, but not of text
    }

    // End of text, but perhaps not of pattern.  Match iff the remaining
    // pattern can match a zero-length string, ie, it's zero or more %'s.
    while pattern.len() > 0 && pattern.next_raw_byte() == b'%' {
        pattern.advance_byte();
    }
    if pattern.len() == 0 {
        return Ok(Matched::True);
    }

    // End of text with no match, so no point in trying later places to start
    // matching this pattern.
    Ok(Matched::Abort)
}

#[derive(Clone)]
struct Bytes<'a> {
    bytes: &'a [u8],
}

impl<'a> Bytes<'a> {
    #[inline]
    const fn from_str(s: &'a str) -> Self {
        Self {
            bytes: s.as_bytes(),
        }
    }

    #[inline]
    const fn from_bytes(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }

    #[inline]
    fn len(&self) -> usize {
        self.bytes.len()
    }

    #[inline]
    fn advance_byte(&mut self) {
        self.bytes = &self.bytes[1..];
    }

    /// Advance a UTF-8 character.
    #[inline]
    fn advance_char(&mut self) {
        self.advance_byte();
        while !self.bytes.is_empty() && (self.raw_byte_at(0) & 0xC0) == 0x80 {
            self.advance_byte();
        }
    }

    #[inline]
    fn raw_byte_at(&self, index: usize) -> u8 {
        self.bytes[index]
    }

    /// Next UTF-8 character.
    #[inline]
    fn next_raw_char(&self) -> char {
        let str = unsafe { std::str::from_utf8_unchecked(self.bytes) };
        str.chars().next().unwrap()
    }

    #[inline]
    fn to_str(&self) -> String {
        let str = unsafe { std::str::from_utf8_unchecked(self.bytes) };
        str.to_string()
    }

    #[inline]
    fn to_vec(&self) -> Vec<u8> {
        self.bytes.into()
    }
}

#[derive(Clone)]
struct StrTraverser<'a> {
    bytes: Bytes<'a>,
}

impl<'a> StrTraverser<'a> {
    #[inline]
    const fn new(s: &'a str) -> Self {
        Self {
            bytes: Bytes::from_str(s),
        }
    }
}

impl<'a> Traverser for StrTraverser<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.bytes.len()
    }

    #[inline]
    fn advance_byte(&mut self) {
        self.bytes.advance_byte();
    }

    #[inline]
    fn advance_char(&mut self) {
        self.bytes.advance_char()
    }

    #[inline]
    fn raw_byte_at(&self, index: usize) -> u8 {
        self.bytes.raw_byte_at(index)
    }

    #[inline]
    fn next_raw_char(&self) -> char {
        self.bytes.next_raw_char()
    }
}

#[derive(Clone)]
struct BytesTraverser<'a> {
    bytes: Bytes<'a>,
}

impl<'a> BytesTraverser<'a> {
    #[inline]
    const fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes: Bytes::from_bytes(bytes),
        }
    }
}

impl<'a> Traverser for BytesTraverser<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.bytes.len()
    }

    #[inline]
    fn advance_byte(&mut self) {
        self.bytes.advance_byte();
    }

    #[inline]
    fn raw_byte_at(&self, index: usize) -> u8 {
        self.bytes.raw_byte_at(index)
    }
}

/// Case-insensitive str traverser
#[derive(Clone)]
struct CiStrTraverser<'a> {
    bytes: Bytes<'a>,
}

impl<'a> CiStrTraverser<'a> {
    #[inline]
    const fn new(s: &'a str) -> Self {
        Self {
            bytes: Bytes::from_str(s),
        }
    }
}

impl<'a> Traverser for CiStrTraverser<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.bytes.len()
    }

    #[inline]
    fn advance_byte(&mut self) {
        self.bytes.advance_byte();
    }

    #[inline]
    fn advance_char(&mut self) {
        self.bytes.advance_char()
    }

    #[inline]
    fn raw_byte_at(&self, index: usize) -> u8 {
        self.bytes.raw_byte_at(index)
    }

    #[inline]
    fn byte_at(&self, index: usize) -> u8 {
        self.raw_byte_at(index).to_ascii_lowercase()
    }

    #[inline]
    fn next_raw_char(&self) -> char {
        self.bytes.next_raw_char()
    }
}

/// Case-insensitive bytes traverser
#[derive(Clone)]
struct CiBytesTraverser<'a> {
    bytes: Bytes<'a>,
}

impl<'a> CiBytesTraverser<'a> {
    #[inline]
    const fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes: Bytes::from_bytes(bytes),
        }
    }
}

impl<'a> Traverser for CiBytesTraverser<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.bytes.len()
    }

    #[inline]
    fn advance_byte(&mut self) {
        self.bytes.advance_byte();
    }

    #[inline]
    fn raw_byte_at(&self, index: usize) -> u8 {
        self.bytes.raw_byte_at(index)
    }

    #[inline]
    fn byte_at(&self, index: usize) -> u8 {
        self.raw_byte_at(index).to_ascii_lowercase()
    }
}

impl<const HAS_ESCAPE: bool> Like<HAS_ESCAPE> for str {
    type Err = InvalidPatternError;

    #[inline]
    fn like(&self, pattern: &Self) -> Result<bool, Self::Err> {
        let mut input = StrTraverser::new(self);
        let mut pattern = StrTraverser::new(pattern);
        let result = like::<_, HAS_ESCAPE>(&mut input, &mut pattern)?;
        Ok(matches!(result, Matched::True))
    }
}

impl<const HAS_ESCAPE: bool> Like<HAS_ESCAPE> for [u8] {
    type Err = InvalidPatternError;

    #[inline]
    fn like(&self, pattern: &Self) -> Result<bool, Self::Err> {
        let mut input = BytesTraverser::new(self);
        let mut pattern = BytesTraverser::new(pattern);
        let result = like::<_, HAS_ESCAPE>(&mut input, &mut pattern)?;
        Ok(matches!(result, Matched::True))
    }
}

impl<const HAS_ESCAPE: bool> ILike<HAS_ESCAPE> for str {
    type Err = InvalidPatternError;

    #[inline]
    fn ilike(&self, pattern: &Self) -> Result<bool, Self::Err> {
        let mut input = CiStrTraverser::new(self);
        let mut pattern = CiStrTraverser::new(pattern);
        let result = like::<_, HAS_ESCAPE>(&mut input, &mut pattern)?;
        Ok(matches!(result, Matched::True))
    }
}

impl<const HAS_ESCAPE: bool> ILike<HAS_ESCAPE> for [u8] {
    type Err = InvalidPatternError;

    #[inline]
    fn ilike(&self, pattern: &Self) -> Result<bool, Self::Err> {
        let mut input = CiBytesTraverser::new(self);
        let mut pattern = CiBytesTraverser::new(pattern);
        let result = like::<_, HAS_ESCAPE>(&mut input, &mut pattern)?;
        Ok(matches!(result, Matched::True))
    }
}

trait Owned {
    fn new(size: usize) -> Self;
    fn append(&mut self, ch: char);
}

trait ToOwned {
    type Owned: Owned;

    fn to_owned(&self) -> Self::Owned;
}

/// Errors which can occur when attempting to convert escape.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum InvalidEscapeError {
    /// Multiple Escape characters error.
    MultiChars,
    /// Error character following Escape.
    InvalidEscape,
}

impl Display for InvalidEscapeError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InvalidEscapeError::MultiChars => {
                write!(f, "escape must be one character")
            }
            InvalidEscapeError::InvalidEscape => {
                write!(
                    f,
                    "missing or illegal character following the escape character"
                )
            }
        }
    }
}

impl Error for InvalidEscapeError {}

fn escape<T, R>(pat: &mut T, esc: &mut T) -> Result<R, InvalidEscapeError>
where
    T: Traverser + ToOwned<Owned = R>,
    R: Owned,
{
    // Worst-case pattern growth is 2x --- unlikely, but it's hardly worth
    // trying to calculate the size more accurately than that.
    let mut result = R::new(pat.len() * 2);

    if esc.len() == 0 {
        // No escape character is wanted.  Double any backslashes in the
        // pattern to make them act like ordinary characters.
        while pat.len() > 0 {
            if pat.next_raw_byte() == b'\\' {
                result.append('\\');
            }
            result.append(pat.next_raw_char());
            pat.advance_char();
        }
    } else {
        // The specified escape must be only a single character.
        let e = esc.next_raw_char();
        esc.advance_char();
        if esc.len() != 0 {
            return Err(InvalidEscapeError::MultiChars);
        }

        // Otherwise, convert occurrences of the specified escape character to
        // '\', and double occurrences of '\' --- unless they immediately
        // follow an escape character!
        let mut afterescape = false;
        while pat.len() > 0 {
            if pat.next_raw_char() == e && !afterescape {
                result.append('\\');
                pat.advance_char();
                if pat.len() == 0 {
                    return Err(InvalidEscapeError::InvalidEscape);
                } else {
                    let next_pat = pat.next_raw_char();
                    if next_pat != '%' && next_pat != '_' && next_pat != e {
                        return Err(InvalidEscapeError::InvalidEscape);
                    }
                }
                afterescape = true;
            } else if pat.next_raw_byte() == b'\\' {
                result.append('\\');
                if !afterescape {
                    result.append('\\');
                }
                pat.advance_char();
                afterescape = false;
            } else {
                result.append(pat.next_raw_char());
                pat.advance_char();
                afterescape = false;
            }
        }
    }
    Ok(result)
}

impl Owned for String {
    fn new(size: usize) -> String {
        String::with_capacity(size)
    }

    fn append(&mut self, ch: char) {
        self.push(ch)
    }
}

impl Owned for Vec<u8> {
    fn new(size: usize) -> Vec<u8> {
        Vec::with_capacity(size)
    }

    fn append(&mut self, ch: char) {
        self.push(ch as u8)
    }
}

impl<'a> ToOwned for StrTraverser<'a> {
    type Owned = String;

    fn to_owned(&self) -> Self::Owned {
        self.bytes.to_str()
    }
}

impl<'a> ToOwned for BytesTraverser<'a> {
    type Owned = Vec<u8>;

    fn to_owned(&self) -> Self::Owned {
        self.bytes.to_vec()
    }
}

impl Escape for str {
    type Err = InvalidEscapeError;
    type Output = String;

    #[inline]
    fn escape(&self, esc: &Self) -> Result<Self::Output, Self::Err> {
        let mut p = StrTraverser::new(self);
        let mut e = StrTraverser::new(esc);
        escape(&mut p, &mut e)
    }
}

impl Escape for [u8] {
    type Err = InvalidEscapeError;
    type Output = Vec<u8>;

    #[inline]
    fn escape(&self, esc: &Self) -> Result<Self::Output, Self::Err> {
        let mut p = BytesTraverser::new(self);
        let mut e = BytesTraverser::new(esc);
        escape(&mut p, &mut e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Debug;

    fn like_test<T, const HAS_ESCAPE: bool>(input: &T, pattern: &T, result: bool)
    where
        T: Like<HAS_ESCAPE> + ?Sized,
        T::Err: Debug,
    {
        assert_eq!(input.like(pattern).unwrap(), result);
        assert_eq!(input.not_like(pattern).unwrap(), !result);
    }

    fn ilike_test<T, const HAS_ESCAPE: bool>(input: &T, pattern: &T, result: bool)
    where
        T: ILike<HAS_ESCAPE> + ?Sized,
        T::Err: Debug,
    {
        assert_eq!(input.ilike(pattern).unwrap(), result);
        assert_eq!(input.not_ilike(pattern).unwrap(), !result);
    }

    fn pattern_error_test<T: Like<true> + ILike<true> + ?Sized>(input: &T, error_pattern: &T) {
        assert!(input.like(error_pattern).is_err());
        assert!(input.not_like(error_pattern).is_err());
        assert!(input.ilike(error_pattern).is_err());
        assert!(input.not_ilike(error_pattern).is_err());
    }

    #[test]
    fn test_pattern_error() {
        // LIKE pattern must not end with escape character;
        // pattern end with escape character will return error.
        pattern_error_test("H", "\\");
        pattern_error_test("Hello,世界!", "Hello,世界\\");
        pattern_error_test(&b"H"[..], b"\\");
        pattern_error_test(&b"Hello!"[..], b"Hello\\");
    }

    #[test]
    fn test_percent_sign() {
        // a percent sign (%) matches any sequence of zero or more characters
        let str = "Hello,世界!";
        like_test::<_, false>(str, "%", true);
        like_test::<_, false>(str, "%%%%%%%%%", true);
        like_test::<_, false>(str, "%%%%%%%%%%", true);
        ilike_test::<_, false>(str, "%", true);
        ilike_test::<_, false>(str, "%%%%%%%%%", true);
        ilike_test::<_, false>(str, "%%%%%%%%%%", true);

        let bytes = &b"Hello!"[..];
        like_test::<_, false>(bytes, b"%", true);
        like_test::<_, false>(bytes, b"%%%%%%", true);
        like_test::<_, false>(bytes, b"%%%%%%%", true);
        ilike_test::<_, false>(bytes, b"%", true);
        ilike_test::<_, false>(bytes, b"%%%%%%", true);
        ilike_test::<_, false>(bytes, b"%%%%%%%", true);

        let str2: &str = "601618";
        let bytes2: &[u8] = b"601618";
        like_test::<_, false>(str2, "%618", true);
        ilike_test::<_, false>(str2, "%618", true);
        like_test::<_, false>(bytes2, b"%618", true);
        ilike_test::<_, false>(bytes2, b"%618", true);

        // Test Utf8
        let str3 = "中文测试";
        like_test::<_, false>(str3, "%测试", true);
        like_test::<_, false>(str3, "中文测试%%", true);
        ilike_test::<_, false>(str3, "%测试", true);
        like_test::<_, false>("中文测试%\\", "中文测试%\\", true);
        ilike_test::<_, false>("中文测试%\\", "中文测试%\\", true);
    }

    #[test]
    fn test_underscore() {
        // An underscore (_) in pattern stands for (matches) any single character
        let str: &str = "Hello,世界!";
        like_test::<_, false>(str, "_", false);
        like_test::<_, false>(str, "________", false);
        like_test::<_, false>(str, "_________", true);
        like_test::<_, false>(str, "__________", false);
        ilike_test::<_, false>(str, "_", false);
        ilike_test::<_, false>(str, "________", false);
        ilike_test::<_, false>(str, "_________", true);
        ilike_test::<_, false>(str, "__________", false);

        let bytes: &[u8] = b"Hello!";
        like_test::<_, false>(bytes, b"_", false);
        like_test::<_, false>(bytes, b"_____", false);
        like_test::<_, false>(bytes, b"______", true);
        like_test::<_, false>(bytes, b"_______", false);
        ilike_test::<_, false>(bytes, b"_", false);
        ilike_test::<_, false>(bytes, b"_____", false);
        ilike_test::<_, false>(bytes, b"______", true);
        ilike_test::<_, false>(bytes, b"_______", false);
    }

    #[test]
    fn test_pattern_without_sign() {
        // If pattern does not contain percent signs or underscores,
        // then the pattern only represents the string itself.
        let str_lower: &str = "hello,世界!";
        let str_upper: &str = "Hello,世界!";
        like_test::<_, false>(str_upper, "Hello", false);
        like_test::<_, false>(str_upper, "Hello,!", false);
        like_test::<_, false>(str_upper, "Hello,世界!", true);
        like_test::<_, false>(str_upper, "hello,世界!", false);
        ilike_test::<_, false>(str_upper, "hello,世界!", true);
        ilike_test::<_, false>(str_lower, "Hello,世界!", true);

        let bytes_lower: &[u8] = b"hello!";
        let bytes_upper: &[u8] = b"Hello!";
        like_test::<_, false>(bytes_upper, b"Hello", false);
        like_test::<_, false>(bytes_upper, b"Hello!", true);
        like_test::<_, false>(bytes_upper, b"hello!", false);
        ilike_test::<_, false>(bytes_upper, b"hello!", true);
        ilike_test::<_, false>(bytes_lower, b"Hello!", true);
    }

    #[test]
    fn test_mixed_pattern() {
        // Mix the string, percent sign(%) and underscores(_) in the input,
        // and make sure the combination works
        let str: &str = "Abc";
        like_test::<_, false>(str, "A%_", true);
        like_test::<_, false>(str, "A_%", true);
        like_test::<_, false>(str, "%b_", true);
        like_test::<_, false>(str, "%_c", true);
        like_test::<_, false>(str, "_b%", true);
        like_test::<_, false>(str, "_%c", true);
        ilike_test::<_, false>(str, "a%_", true);
        ilike_test::<_, false>(str, "a_%", true);
        ilike_test::<_, false>(str, "%B_", true);
        ilike_test::<_, false>(str, "%_C", true);
        ilike_test::<_, false>(str, "_B%", true);
        ilike_test::<_, false>(str, "_%C", true);

        let bytes: &[u8] = b"Abc";
        like_test::<_, false>(bytes, b"A%_", true);
        like_test::<_, false>(bytes, b"A_%", true);
        like_test::<_, false>(bytes, b"%b_", true);
        like_test::<_, false>(bytes, b"%_c", true);
        like_test::<_, false>(bytes, b"_b%", true);
        like_test::<_, false>(bytes, b"_%c", true);
        ilike_test::<_, false>(bytes, b"a%_", true);
        ilike_test::<_, false>(bytes, b"a_%", true);
        ilike_test::<_, false>(bytes, b"%B_", true);
        ilike_test::<_, false>(bytes, b"%_C", true);
        ilike_test::<_, false>(bytes, b"_B%", true);
        ilike_test::<_, false>(bytes, b"_%C", true);
    }

    #[test]
    fn test_like_escape() {
        let escape = ",";
        let pattern = "Hello,,世界!".escape(escape).unwrap();
        like_test::<_, true>("Hello,世界!", pattern.as_str(), true);
        ilike_test::<_, true>("hello,世界!", pattern.as_str(), true);

        // No escape in pattern
        let escape = "?";
        let pattern = "Hello\\世界!".escape(escape).unwrap();
        like_test::<_, true>("Hello\\世界!", pattern.as_str(), true);
        ilike_test::<_, true>("hello\\世界!", pattern.as_str(), true);

        let pattern = "Hello,世界!\\".escape(escape).unwrap();
        like_test::<_, true>("Hello,世界!\\", pattern.as_str(), true);
        ilike_test::<_, true>("hello,世界!\\", pattern.as_str(), true);

        let escape = "\\";
        let pattern = "Hello,世界!".escape(escape).unwrap();
        like_test::<_, true>("Hello,世界!", pattern.as_str(), true);
        ilike_test::<_, true>("hello,世界!", pattern.as_str(), true);
    }

    fn escape_test<T: Escape + ?Sized, R: Into<T::Output>>(input: &T, escape: &T, result: R)
    where
        T::Output: Debug + PartialEq,
        T::Err: Debug,
    {
        assert_eq!(input.escape(escape).unwrap(), result.into());
    }

    fn escape_error_test<T: Escape + ?Sized>(input: &T, error_escape: &T) {
        assert!(input.escape(error_escape).is_err());
    }

    #[test]
    fn test_escape_error() {
        // Escape string must be empty or one character;
        // if Escape string is more than one character will return error.
        escape_error_test("Hello,世界!", ",!");
        escape_error_test("Hello,世界!", "!");
        escape_error_test("Hello,世界\\", "\\");
        escape_error_test("Hello,世界\\1", "\\");
        escape_error_test("Hello,世界", "界");
        escape_error_test(&b"Hello,World!"[..], b",!");
    }

    #[test]
    fn test_escape() {
        let str: &str = "Hello,世界!";
        escape_test(str, "", str);
        escape_test(str, "\\", str);
        escape_test(str, "?", "Hello,世界!");
        escape_test("HHello,世界!", "H", "\\Hello,世界!");
        escape_test("Hello,,世界!", ",", "Hello\\,世界!");
        escape_test("Hello,世界!!", "!", "Hello,世界\\!");
        escape_test("Hello,世世界!", "世", "Hello,\\世界!");
        escape_test("Hello,,,,世界!", ",", "Hello\\,\\,世界!");
        escape_test("Hello!!世界!!", "!", "Hello\\!世界\\!");
        escape_test("Hello\\!世界!", "", "Hello\\\\!世界!");
        escape_test("Hello$$%$$_世界!", "$", "Hello\\$%\\$_世界!");

        let bytes: &[u8] = b"Hello,World!";
        escape_test(bytes, b"", bytes);
        escape_test(bytes, b"\\", bytes);
        escape_test(bytes, b"?", &b"Hello,World!"[..]);
        escape_test(&b"HHello,World!"[..], b"H", &b"\\Hello,World!"[..]);
        escape_test(&b"Hello,,World!"[..], b",", &b"Hello\\,World!"[..]);
        escape_test(&b"Hello,World!!"[..], b"!", &b"Hello,World\\!"[..]);
        escape_test(&b"Hello,,,,World!"[..], b",", &b"Hello\\,\\,World!"[..]);
        escape_test(&b"Hello!!World!!"[..], b"!", &b"Hello\\!World\\!"[..]);
        escape_test(&b"Hello\\World!"[..], b"", &b"Hello\\\\World!"[..]);
        escape_test(&b"Hello$$%$$_World!"[..], b"$", &b"Hello\\$%\\$_World!"[..]);
    }
}
