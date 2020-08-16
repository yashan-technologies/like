# like

[![Apache-2.0 licensed](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![Crate](https://img.shields.io/crates/v/like.svg)](https://crates.io/crates/like)
[![API](https://docs.rs/like/badge.svg)](https://docs.rs/like)

A SQL `like` style pattern matching.

## Usage

To do a patten matching, use `Like`:

```Rust
use like::Like;

assert!("Hello, world!".like("Hello%").unwrap());
```

To do a case-insensitive pattern matching, use `ILike`:

```Rust
use like::ILike;

assert!("Hello, world!".ilike("HELLO%").unwrap());
```

To convert the pattern to use standard backslash escape convention, use `Escape`:

```Rust
use like::Escape;

assert_eq!("Hello$%".escape("$").unwrap(), "Hello\\%");
```

## License

This project is licensed under the Apache-2.0 license ([LICENSE](LICENSE) or http://www.apache.org/licenses/LICENSE-2.0).

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in `like` by you, shall be licensed as Apache-2.0, without any additional
terms or conditions.
