#![deny(missing_docs)]
#![feature(core)]

//! A simple library to read tokens using look ahead

extern crate range;

use range::Range;

/// Reads an expected token, return `None` if it does not match.
pub fn token(token: &str, chars: &[char], offset: usize) -> Option<Range> {
    if chars.len() < token.len() { return None; }
    for (i, c) in token.chars().enumerate() {
        if c != chars[i] { return None; }
    }
    return Some(Range::new(offset, token.len()))
}

/// Reads a token until any character in string or whitespace.
pub fn until_any_or_whitespace(
    any: &str,
    chars: &[char],
    offset: usize
) -> Range {
    for (i, &c) in chars.iter().enumerate() {
        if c.is_whitespace() {
            return Range::new(offset, i)
        }
        for b in any.chars() {
            if c == b { return Range::new(offset, i) }
        }
    }
    Range::new(offset, chars.len())
}

/// Reads whitespace.
pub fn whitespace(chars: &[char], offset: usize) -> Range {
    for (i, &c) in chars.iter().enumerate() {
        if !c.is_whitespace() { return Range::new(offset, i) }
    }
    Range::new(offset, chars.len())
}

/// Reads string with character escapes.
pub fn string(chars: &[char], offset: usize) -> Option<Range> {
    if chars[0] != '"' { return None; }
    let mut escape = false;
    for i in 1..chars.len() - 1 {
        if chars[i] == '\\' { escape = true; continue; }
        if !escape && chars[i] == '"' { return Some(Range::new(offset, i)) }
    }
    if chars[chars.len() - 1] == '"' {
        return Some(Range::new(offset, chars.len()))
    } else {
        return None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use range::Range;

    #[test]
    pub fn test_token() {
        let text = "one day, a nice day".chars().collect::<Vec<char>>();
        let res = token("one", &text[], 0);
        assert_eq!(res, Some(Range::new(0, 3)));
        let res = token("two", &text[], 0);
        assert_eq!(res, None);
    }

    #[test]
    pub fn test_until_any_or_whitespace() {
        let text = "one day, a nice day".chars().collect::<Vec<char>>();
        let res = until_any_or_whitespace(",", &text[], 0);
        assert_eq!(res, Range::new(0, 3));
        let res = until_any_or_whitespace(",", &text[3..], 0);
        assert_eq!(res, Range::empty(0));
    }

    #[test]
    pub fn test_whitespace() {
        let text = "   123".chars().collect::<Vec<char>>();
        let res = whitespace(&text[], 0);
        assert_eq!(res, Range::new(0, 3));
    }

    #[test]
    pub fn test_string() {
        let text = "\"hello\"".chars().collect::<Vec<char>>();
        let res = string(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 7)));

        let text = "\"he\\\"llo\"".chars().collect::<Vec<char>>();
        let res = string(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 9)));

        let text = "\"he\"llo\"".chars().collect::<Vec<char>>();
        let res = string(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 3)));
    }
}
