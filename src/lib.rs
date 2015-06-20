#![deny(missing_docs)]

//! A simple library to read tokens using look ahead

extern crate range;

use std::fmt::{ Display, Formatter };
use std::fmt::Error as FormatError;
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
/// Returns `(range, None)` if stopping at whitespace or end of characters.
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

/// Reads token until any character in string.
/// Returns `(range, None)` if stopping at end of characters.
/// Returns `(range, Some(x))` if stopping at a character.
pub fn until_any(
    any: &str,
    chars: &[char],
    offset: usize
) -> (Range, Option<usize>) {
    for (i, &c) in chars.iter().enumerate() {
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
    if chars.len() == 0 || chars[0] != '"' { return None; }
    let mut escape = false;
    for i in 1..chars.len() - 1 {
        if chars[i] == '\\' { escape = true; continue; }
        if !escape && chars[i] == '"' { return Some(Range::new(offset, i + 1)) }
        if escape { escape = false; }
    }
    if !escape && chars[chars.len() - 1] == '"' {
        return Some(Range::new(offset, chars.len()))
    } else {
        return None
    }
}

/// Contains errors when parsing a string.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
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

impl ParseStringError {
    /// Gets the range of the error.
    pub fn range(&self) -> Range {
        match self {
            &ParseStringError::ExpectedFourHexadecimals(r) => r,
            &ParseStringError::ExpectedHexadecimal(r) => r,
            &ParseStringError::ExpectedValidUnicode(r) => r,
            &ParseStringError::ExpectedValidEscapeCharacter(r) => r,
        }
    }
}

impl Display for ParseStringError {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FormatError> {
        match self {
            &ParseStringError::ExpectedFourHexadecimals(_) =>
                fmt.write_str("Expected four hexadecimals xxxx 0-9A-F"),
            &ParseStringError::ExpectedHexadecimal(_) =>
                fmt.write_str("Expected hexadecimal 0-9A-F"),
            &ParseStringError::ExpectedValidUnicode(_) =>
                fmt.write_str("Expected valid unicode"),
            &ParseStringError::ExpectedValidEscapeCharacter(_) =>
                fmt.write_str("Expected valid escape character '\"\\/bfnrtu'"),
        }
    }
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

/// The settings for reading numbers.
#[derive(Copy, Clone, Debug)]
pub struct NumberSettings {
    /// Whether to allow underscore in number.
    pub allow_underscore: bool,
}

/// Reads number.
pub fn number(
    settings: &NumberSettings,
    chars: &[char],
    offset: usize
) -> Option<Range> {
    let mut has_sign = false;
    let mut has_decimal_separator = false;
    let mut has_scientific = false;
    let mut has_exponent_sign = false;
    let mut has_digit = false;
    for (i, &c) in chars.iter().enumerate() {
        if !has_sign {
            has_sign = true;
            if c == '+' || c == '-' { continue; }
        }
        if c.is_digit(10) {
            has_digit = true;
            continue;
        }
        if has_digit && settings.allow_underscore && c == '_' { continue; }
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

/// Error when parsing number.
#[derive(Copy, Clone, Debug)]
pub enum ParseNumberError {
    /// The number was empty.
    Empty,
    /// The number is of invalid format.
    Invalid,
    /// The number overflowed to infinity.
    Infinity,
    /// The number overflowed to negative infinity.
    NegInfinity,
}

/// Parses number.
pub fn parse_number(src: &str) -> Result<f64, ParseNumberError> {
    fn slice_shift_char(src: &str) -> Option<(char, &str)> {
        src.chars().nth(0).map(|ch| (ch, &src[1..]))
    }

    let radix: u32 = 10;
    let (is_positive, src) =  match slice_shift_char(src) {
        None             => return Err(ParseNumberError::Empty),
        Some(('-', ""))  => return Err(ParseNumberError::Empty),
        Some(('-', src)) => (false, src),
        Some((_, _))     => (true,  src),
    };

    // The significand to accumulate
    let mut sig = if is_positive { 0.0 } else { -0.0 };
    // Necessary to detect overflow
    let mut prev_sig = sig;
    let mut cs = src.chars().enumerate();
    // Exponent prefix and exponent index offset
    let mut exp_info = None::<(char, usize)>;

    // Parse the integer part of the significand
    for (i, c) in cs.by_ref() {
        match c.to_digit(radix) {
            Some(digit) => {
                // shift significand one digit left
                sig = sig * (radix as f64);

                // add/subtract current digit depending on sign
                if is_positive {
                    sig = sig + ((digit as isize) as f64);
                } else {
                    sig = sig - ((digit as isize) as f64);
                }

                // Detect overflow by comparing to last value, except
                // if we've not seen any non-zero digits.
                if prev_sig != 0.0 {
                    if is_positive && sig <= prev_sig
                        { return Err(ParseNumberError::Infinity); }
                    if !is_positive && sig >= prev_sig
                        { return Err(ParseNumberError::NegInfinity); }

                    // Detect overflow by reversing the shift-and-add process
                    if is_positive && (prev_sig != (sig - digit as f64) / radix as f64)
                        { return Err(ParseNumberError::Infinity); }
                    if !is_positive && (prev_sig != (sig + digit as f64) / radix as f64)
                        { return Err(ParseNumberError::NegInfinity); }
                }
                prev_sig = sig;
            },
            None => match c {
                'e' | 'E' | 'p' | 'P' => {
                    exp_info = Some((c, i + 1));
                    break;  // start of exponent
                },
                '.' => {
                    break;  // start of fractional part
                },
                _ => {
                    return Err(ParseNumberError::Invalid);
                },
            },
        }
    }

    // If we are not yet at the exponent parse the fractional
    // part of the significand
    if exp_info.is_none() {
        let mut power = 1.0;
        for (i, c) in cs.by_ref() {
            match c.to_digit(radix) {
                Some(digit) => {
                    // Decrease power one order of magnitude
                    power = power / (radix as f64);
                    // add/subtract current digit depending on sign
                    sig = if is_positive {
                        sig + (digit as f64) * power
                    } else {
                        sig - (digit as f64) * power
                    };
                    // Detect overflow by comparing to last value
                    if is_positive && sig < prev_sig
                        { return Err(ParseNumberError::Infinity); }
                    if !is_positive && sig > prev_sig
                        { return Err(ParseNumberError::NegInfinity); }
                    prev_sig = sig;
                },
                None => match c {
                    'e' | 'E' | 'p' | 'P' => {
                        exp_info = Some((c, i + 1));
                        break; // start of exponent
                    },
                    _ => {
                        return Err(ParseNumberError::Invalid);
                    },
                },
            }
        }
    }

    // Parse and calculate the exponent
    let exp = match exp_info {
        Some((c, offset)) => {
            let base = match c {
                'E' | 'e' if radix == 10 => 10.0,
                _ => return Err(ParseNumberError::Invalid),
            };

            // Parse the exponent as decimal integer
            let src = &src[offset..];
            let (is_positive, exp) = match slice_shift_char(src) {
                Some(('-', src)) => (false, src.parse::<usize>()),
                Some(('+', src)) => (true,  src.parse::<usize>()),
                Some((_, _))     => (true,  src.parse::<usize>()),
                None             => return Err(ParseNumberError::Invalid),
            };

            match (is_positive, exp) {
                (true,  Ok(exp)) => f64::powi(base, exp as i32),
                (false, Ok(exp)) => 1.0 / base.powi(exp as i32),
                (_, Err(_))      => return Err(ParseNumberError::Invalid),
            }
        },
        None => 1.0, // no exponent
    };

    Ok(sig * exp)

}

#[cfg(test)]
mod tests {
    use super::*;
    use range::Range;

    #[test]
    pub fn test_token() {
        let text = "one day, a nice day".chars().collect::<Vec<char>>();
        let res = token("one", &text, 0);
        assert_eq!(res, Some(Range::new(0, 3)));
        let res = token("two", &text, 0);
        assert_eq!(res, None);
    }

    #[test]
    pub fn test_until_any_or_whitespace() {
        let text = "one day, a nice day".chars().collect::<Vec<char>>();
        let res = until_any_or_whitespace(",", &text, 0);
        assert_eq!(res, (Range::new(0, 3), None));
        let res = until_any_or_whitespace(",", &text[3..], 3);
        assert_eq!(res, (Range::empty(3), None));
        let res = until_any_or_whitespace(",", &text[4..], 4);
        assert_eq!(res, (Range::new(4, 3), Some(0)));
    }

    #[test]
    pub fn test_until_any() {
        let text = "one day, a nice day".chars().collect::<Vec<char>>();
        let res = until_any(",", &text, 0);
        assert_eq!(res, (Range::new(0, 7), Some(0)));
        let res = until_any(",", &text[3..], 3);
        assert_eq!(res, (Range::new(3, 4), Some(0)));
        let res = until_any(",", &text[8..], 8);
        assert_eq!(res, (Range::new(8, 11), None));
    }

    #[test]
    pub fn test_whitespace() {
        let text = "   123".chars().collect::<Vec<char>>();
        let res = whitespace(&text, 0);
        assert_eq!(res, Range::new(0, 3));
    }

    #[test]
    pub fn test_string() {
        let text = "\"hello\"".chars().collect::<Vec<char>>();
        let res = string(&text, 0);
        assert_eq!(res, Some(Range::new(0, 7)));
        let txt = parse_string(&text, 0, res.unwrap().next_offset()).ok().unwrap();
        assert_eq!(txt, "hello");

        let text = "\"he\\\"llo\"".chars().collect::<Vec<char>>();
        let res = string(&text, 0);
        assert_eq!(res, Some(Range::new(0, 9)));
        let txt = parse_string(&text, 0, res.unwrap().next_offset());
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "he\"llo");

        let text = "\"he\"llo\"".chars().collect::<Vec<char>>();
        let res = string(&text, 0);
        assert_eq!(res, Some(Range::new(0, 4)));
        let txt = parse_string(&text, 0, res.unwrap().next_offset());
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "he");

        let text = "\"hello\\\"".chars().collect::<Vec<char>>();
        let res = string(&text, 0);
        assert_eq!(res, None);
    }

    #[test]
    pub fn test_number() {
        let settings = NumberSettings { allow_underscore: false };

        let res: f64 = parse_number("20").unwrap();
        assert_eq!(res, 20.0);
        let res: f64 = parse_number("-20").unwrap();
        assert_eq!(res, -20.0);
        let res: f64 = parse_number("2e2").unwrap();
        assert_eq!(res, 2e2);
        let res: f64 = parse_number("2.5").unwrap();
        assert_eq!(res, 2.5);
        let res: f64 = "2.5e2".parse().unwrap();
        assert_eq!(res, 2.5e2);
        let res: f64 = parse_number("2.5E2").unwrap();
        assert_eq!(res, 2.5E2);
        let res: f64 = parse_number("2.5E-2").unwrap();
        assert_eq!(res, 2.5E-2);

        let text = "20".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 2)));

        let text = "-20".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2e2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5e2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E-2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 6)));
    }

    #[test]
    pub fn test_underscore_number() {
        let settings = NumberSettings { allow_underscore: true };

        let _: f64 = "20".parse().unwrap();
        let _: f64 = "-20".parse().unwrap();
        let _: f64 = "2e2".parse().unwrap();
        let _: f64 = "2.5".parse().unwrap();
        let _: f64 = "2.5e2".parse().unwrap();
        let _: f64 = "2.5E2".parse().unwrap();
        let _: f64 = "2.5E-2".parse().unwrap();

        let text = "20".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 2)));

        let text = "-20".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2e2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5e2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E-2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 6)));

        let text = "_2.5E-2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, None);

        let text = "2_.5E-2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 7)));

        let text = "2_000_000.5E-2".chars().collect::<Vec<char>>();
        let res = number(&settings, &text, 0);
        assert_eq!(res, Some(Range::new(0, 14)));
    }
}
