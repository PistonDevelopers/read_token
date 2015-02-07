#![deny(missing_docs)]
#![feature(core)]

//! A simple library to read tokens using look ahead

extern crate range;

use range::Range;

/// Reads an expected token, return `None` if it does not match.
pub fn token(token: &str, chars: &[char], offset: usize) -> Option<Range> {
    if chars.len() < token.len() { return None; }
    for (i, c) in token.chars().enumerate() {
        if c == chars[i] { continue; }
        return None;
    }
    return Some(Range::new(offset, token.len()))
}
