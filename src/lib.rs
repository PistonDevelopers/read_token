#![deny(missing_docs)]
#![feature(core, unicode)]

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
/// Returns `(range, None)` if stopping at whitespace.
/// Returns `(range, Some(x))` if stopping at a character.
pub fn until_any_or_whitespace(
    any: &str,
    chars: &[char],
    offset: usize
) -> (Range, Option<usize>) {
    for (i, &c) in chars.iter().enumerate() {
        if c.is_whitespace() {
            return (Range::new(offset, i), None)
        }
        for (j, b) in any.chars().enumerate() {
            if c == b {
                return (Range::new(offset, i), Some(j))
            }
        }
    }
    (Range::new(offset, chars.len()), None)
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
        if !escape && chars[i] == '"' { return Some(Range::new(offset, i + 1)) }
    }
    if chars[chars.len() - 1] == '"' {
        return Some(Range::new(offset, chars.len()))
    } else {
        return None
    }
}

/// Contains errors when parsing a string.
#[derive(Copy, Debug)]
pub enum ParseStringError {
    /// Expected four hexadecimals, found less characters
    ExpectedFourHexadecimals(Range),
    /// Expected character `0-9a-fA-F`
    ExpectedHexadecimal(Range),
    /// Found four hexadecimals, but not an invalid unicode character
    ExpectedValidUnicode(Range),
    /// A character escape `\x` is invalid
    ExpectedValidEscapeCharacter(Range),
}

/// Parses four unicode characters in hexadecimal format.
pub fn parse_unicode(
    chars: &[char],
    offset: usize
) -> Result<char, ParseStringError> {
    use std::char;

    if chars.len() < 4 {
        return Err(ParseStringError::ExpectedFourHexadecimals(
            Range::new(offset, chars.len())
        ));
    }

    let mut u: [u32; 4] = [0; 4];
    for (i, c) in u.iter_mut().enumerate() {
        match chars[i].to_digit(16) {
            Some(x) => *c = x as u32,
            None => {
                return Err(ParseStringError::ExpectedHexadecimal(
                    Range::new(offset + i, 1)
                ))
            }
        }
    }
    let code = (u[0] << 12) | (u[1] << 8) | (u[2] << 4) | u[3];
    match char::from_u32(code) {
        Some(x) => Ok(x),
        None => Err(ParseStringError::ExpectedValidUnicode(
            Range::new(offset, 4)
        ))
    }
}

/// Parses string into a real string according to the JSON standard.
///
/// Assumes the string starts and ends with double-quotes.
/// `offset` is the location at the start of the slice.
/// `next_offset` is the location where the string ends.
pub fn parse_string(
    chars: &[char],
    offset: usize,
    next_offset: usize,
) -> Result<String, ParseStringError> {
    let mut escape = false;
    let length = next_offset - offset - 2;
    let mut txt = String::with_capacity(length);
    for (i, &c) in chars[1..length + 1].iter().enumerate() {
        if c == '\\' { escape = true; continue; }
        if escape {
            escape = false;
            txt.push(match c {
                '\"' => '"',
                '\\' => '\\',
                '/' => '/',
                'b' => '\u{0008}',
                'f' => '\u{000c}',
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                'u' => {
                    let offset = offset + 1 + i;
                    match parse_unicode(&chars[offset..], offset) {
                        Ok(x) => x,
                        Err(err) => return Err(err)
                    }
                }
                _ => {
                    return Err(ParseStringError::ExpectedValidEscapeCharacter(
                        Range::new(offset + i + 1, 1)
                    ));
                }
            })
        } else {
            txt.push(c)
        }
    }
    Ok(txt)
}

/// Reads number.
pub fn number(chars: &[char], offset: usize) -> Option<Range> {
    let mut has_sign = false;
    let mut has_decimal_separator = false;
    let mut has_scientific = false;
    let mut has_exponent_sign = false;
    for (i, &c) in chars.iter().enumerate() {
        if !has_sign {
            has_sign = true;
            if c == '+' || c == '-' { continue; }
        }
        if c.is_digit(10) { continue; }
        if !has_decimal_separator && c == '.' {
            has_decimal_separator = true;
            continue;
        }
        if !has_scientific && (c == 'e' || c == 'E') {
            has_scientific = true;
            continue;
        }
        if has_scientific && !has_exponent_sign {
            has_exponent_sign = true;
            if c == '+' || c == '-' { continue; }
        }
        if i > 0 { return Some(Range::new(offset, i)) }
        else { return None }
    }
    if chars.len() > 0 { return Some(Range::new(offset, chars.len())) }
    else { return None }
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
        assert_eq!(res, (Range::new(0, 3), None));
        let res = until_any_or_whitespace(",", &text[3..], 3);
        assert_eq!(res, (Range::empty(3), None));
        let res = until_any_or_whitespace(",", &text[4..], 4);
        assert_eq!(res, (Range::new(4, 3), Some(0)));
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
        let txt = parse_string(&text[], 0, res.unwrap().next_offset()).ok().unwrap();
        assert_eq!(txt, "hello");

        let text = "\"he\\\"llo\"".chars().collect::<Vec<char>>();
        let res = string(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 9)));
        let txt = parse_string(&text[], 0, res.unwrap().next_offset());
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "he\"llo");

        let text = "\"he\"llo\"".chars().collect::<Vec<char>>();
        let res = string(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 4)));
        let txt = parse_string(&text[], 0, res.unwrap().next_offset());
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "he");
    }

    #[test]
    pub fn test_number() {
        let _: f64 = "20".parse().unwrap();
        let _: f64 = "-20".parse().unwrap();
        let _: f64 = "2e2".parse().unwrap();
        let _: f64 = "2.5".parse().unwrap();
        let _: f64 = "2.5e2".parse().unwrap();
        let _: f64 = "2.5E2".parse().unwrap();
        let _: f64 = "2.5E-2".parse().unwrap();

        let text = "20".chars().collect::<Vec<char>>();
        let res = number(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 2)));

        let text = "-20".chars().collect::<Vec<char>>();
        let res = number(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2e2".chars().collect::<Vec<char>>();
        let res = number(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5".chars().collect::<Vec<char>>();
        let res = number(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5e2".chars().collect::<Vec<char>>();
        let res = number(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E2".chars().collect::<Vec<char>>();
        let res = number(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E-2".chars().collect::<Vec<char>>();
        let res = number(&text[], 0);
        assert_eq!(res, Some(Range::new(0, 6)));
    }
}
