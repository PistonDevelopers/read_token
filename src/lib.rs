#![deny(missing_docs)]

//! A simple library to read tokens using look ahead

extern crate range;

use std::fmt::{ Display, Formatter };
use std::fmt::Error as FormatError;
use range::Range;

/// Stores the state of parsing.
#[derive(Copy, Clone, Debug)]
pub struct ReadToken<'a> {
    chars: &'a [char],
    offset: usize,
}

impl<'a> ReadToken<'a> {
    /// Creates a new state.
    pub fn new(chars: &'a [char], offset: usize) -> ReadToken<'a> {
        ReadToken {
            chars: chars,
            offset: offset,
        }
    }

    /// Consumes a range of characters.
    pub fn consume(self, range: Range) -> ReadToken<'a> {
        let next_offset = range.next_offset();
        ReadToken {
            chars: &self.chars[next_offset - self.offset..],
            offset: next_offset
        }
    }

    /// Take n characters for separate reading.
    pub fn take(&self, n: usize) -> ReadToken<'a> {
        ReadToken {
            chars: &self.chars[..n],
            offset: self.offset
        }
    }

    /// Reads a raw string.
    pub fn raw_string(&self, n: usize) -> String {
        let mut text = String::with_capacity(n);
        for c in self.chars.iter().take(n) {
            text.push(*c);
        }
        text
    }

    /// Returns whether a range of characters ended with newline character
    /// followed by whitespace.
    fn ended_with_newline(&self, range: Range) -> bool {
        let end = range.next_offset() - self.offset;
        let last_new_line = self.chars[..end].iter()
            .rev()
            .take_while(|&c| *c != '\n' && c.is_whitespace())
            .count();
        if end < last_new_line + 1
        || self.chars[end - last_new_line - 1] != '\n' { false }
        else { true }
    }

    /// Read lines until closure returns `None`.
    /// Returns `Ok(range)` of the successful read lines.
    /// Returns `Err(range)` when expected new line.
    pub fn lines<F>(&self, mut f: F) -> Result<Range, Range>
        where F: FnMut(&ReadToken) -> Option<Range>
    {
        let mut read_token = *self;
        let mut new_lines = true;
        loop {
            let len = read_token.chars.iter()
                .take_while(|&c| *c != '\n' && c.is_whitespace())
                .count();
            if len == read_token.chars.len() {
                read_token.offset += len;
                break;
            } else if read_token.chars[len] == '\n' {
                read_token.chars = &read_token.chars[len + 1..];
                read_token.offset += len + 1;
                new_lines |= true;
            } else {
                if new_lines {
                    match f(&read_token) {
                        None => { break; }
                        Some(range) => {
                            // Find whether a new line occured at the end.
                            // If it did, we do not require a new line before
                            // calling the closure.
                            new_lines = read_token.ended_with_newline(range);
                            read_token = read_token.consume(range);
                        }
                    }
                } else {
                    return Err(Range::empty(read_token.offset));
                }
            }
        }
        Ok(read_token.subtract(self))
    }

    /// Returns the difference in offset.
    #[inline(always)]
    pub fn subtract(&self, rhs: &Self) -> Range {
        Range::new(rhs.offset, self.offset - rhs.offset)
    }

    /// Returns an empty range at current offset.
    #[inline(always)]
    pub fn start(&self) -> Range {
        Range::empty(self.offset)
    }

    /// Peek a number of characters ahead.
    #[inline(always)]
    pub fn peek(&self, n: usize) -> Range {
        Range::new(self.offset, n)
    }

    /// Reads an expected tag, returns character range and new state.
    /// Returns old state when fail to match tag.
    pub fn tag(&self, tag: &str) -> Option<Range> {
        let n = tag.chars().count();
        if self.chars.len() < n { return None; }
        for (i, c) in tag.chars().enumerate() {
            if c != self.chars[i] { return None; }
        }
        return Some(self.peek(n));
    }

    /// Reads a token until any character in string or whitespace.
    /// Returns `(range, None)` if stopping at whitespace
    /// or end of characters.
    /// Returns `(range, Some(x))` if stopping at a character.
    pub fn until_any_or_whitespace(&self, any: &str) -> (Range, Option<usize>) {
        for (i, &c) in self.chars.iter().enumerate() {
            if c.is_whitespace() { return (self.peek(i), None) }
            for (j, b) in any.chars().enumerate() {
                if c == b { return (self.peek(i), Some(j)) }
            }
        }
        (self.peek(self.chars.len()), None)
    }

    /// Reads token until any character in string.
    /// Returns `(new_state, range, None)` if stopping at end of characters.
    /// Returns `(new_state, range, Some(x))` if stopping at a character.
    pub fn until_any(&self, any: &str) -> (Range, Option<usize>) {
        for (i, &c) in self.chars.iter().enumerate() {
            for (j, b) in any.chars().enumerate() {
                if c == b { return (self.peek(i), Some(j)) }
            }
        }
        (self.peek(self.chars.len()), None)
    }

    /// Reads whitespace.
    pub fn whitespace(&self) -> Range {
        for (i, &c) in self.chars.iter().enumerate() {
            if !c.is_whitespace() { return self.peek(i); }
        }
        self.peek(self.chars.len())
    }

    /// Reads string with character escapes.
    pub fn string(&self) -> Option<Range> {
        let n = self.chars.len();
        if n == 0 || self.chars[0] != '"' { return None; }
        let mut escape = false;
        for i in 1..n - 1 {
            if self.chars[i] == '\\' { escape = true; continue; }
            if !escape && self.chars[i] == '"' {
                return Some(self.peek(i + 1))
            }
            if escape { escape = false; }
        }
        if !escape && self.chars[n - 1] == '"' {
            return Some(self.peek(n))
        } else {
            return None
        }
    }

    /// Reads number.
    pub fn number(&self, settings: &NumberSettings) -> Option<Range> {
        let mut has_sign = false;
        let mut has_decimal_separator = false;
        let mut has_scientific = false;
        let mut has_exponent_sign = false;
        let mut has_digit = false;
        for (i, &c) in self.chars.iter().enumerate() {
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
            if i > 0 { return Some(self.peek(i)); }
            else { return None }
        }
        if self.chars.len() > 0 { return Some(self.peek(self.chars.len())); }
        else { return None }
    }

    /// Parses four unicode characters in hexadecimal format.
    pub fn parse_unicode(&self) -> Result<char, Range<ParseStringError>> {
        use std::char;

        if self.chars.len() < 4 {
            return Err(Range::new(self.offset, self.chars.len())
                .wrap(ParseStringError::ExpectedFourHexadecimals));
        }

        let mut u: [u32; 4] = [0; 4];
        for (i, c) in u.iter_mut().enumerate() {
            match self.chars[i].to_digit(16) {
                Some(x) => *c = x as u32,
                None => {
                    return Err(Range::new(self.offset + i, 1)
                        .wrap(ParseStringError::ExpectedHexadecimal))
                }
            }
        }
        let code = (u[0] << 12) | (u[1] << 8) | (u[2] << 4) | u[3];
        match char::from_u32(code) {
            Some(x) => Ok(x),
            None => Err(Range::new(self.offset, 4)
                .wrap(ParseStringError::ExpectedValidUnicode))
        }
    }

    /// Parses string into a real string according to the JSON standard.
    ///
    /// Assumes the string starts and ends with double-quotes.
    /// `n` is the number of characters to read and must be at least 2,
    /// because the string is surrounded by quotes.
    pub fn parse_string(&self, n: usize)
    -> Result<String, Range<ParseStringError>> {
        let mut escape = false;
        let length = n - 2;
        let mut txt = String::with_capacity(length);
        for (i, &c) in self.chars[1..length + 1].iter().enumerate() {
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
                        let offset = self.offset + 1 + i;
                        match ReadToken::new(&self.chars[offset..], offset)
                            .parse_unicode() {
                            Ok(x) => x,
                            Err(err) => return Err(err)
                        }
                    }
                    _ => {
                        return Err(Range::new(self.offset + i + 1, 1)
                            .wrap(ParseStringError::ExpectedValidEscapeCharacter));
                    }
                })
            } else {
                txt.push(c)
            }
        }
        Ok(txt)
    }

    /// Parses number from n characters.
    pub fn parse_number(&self, settings: &NumberSettings, n: usize)
    -> Result<f64, ParseNumberError> {
        #[inline(always)]
        fn slice_shift_char(src: &[char]) -> Option<(char, &[char])> {
            if src.len() == 0 { None }
            else { Some((src[0], &src[1..])) }
        }

        #[inline(always)]
        fn parse_u64(settings: &NumberSettings, src: &[char]) -> Result<u64, ()> {
            let mut res: u64 = 0;
            for &c in src {
                if settings.allow_underscore && c == '_' { continue; }
                res *= 10;
                if let Some(digit) = to_digit(c) {
                    res += digit as u64;
                } else {
                    return Err(())
                }
            }
            Ok(res)
        }

        #[inline(always)]
        fn to_digit(c: char) -> Option<u32> {
            if c >= '0' && c <= '9' { Some(c as u32 - '0' as u32) }
            else { None }
        }

        let radix: u32 = 10;
        let src = &self.chars[..n];
        let (is_positive, src) =  match slice_shift_char(src) {
            None => {
                return Err(ParseNumberError::ExpectedDigits);
            }
            Some(('-', src)) if src.len() == 0 => {
                return Err(ParseNumberError::ExpectedDigits);
            }
            Some(('-', src)) => (false, src),
            Some((_, _))     => (true,  src),
        };

        // The significand to accumulate
        let mut sig = if is_positive { 0.0 } else { -0.0 };
        // Necessary to detect overflow
        let mut prev_sig = sig;
        let mut cs = src.iter().enumerate();
        // Exponent prefix and exponent index offset
        let mut exp_info = None::<(char, usize)>;

        // Parse the integer part of the significand
        for (i, &c) in cs.by_ref() {
            if settings.allow_underscore && c == '_' { continue; }
            match to_digit(c) {
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
                            { return Err(ParseNumberError::OverflowInfinity); }
                        if !is_positive && sig >= prev_sig
                            { return Err(ParseNumberError::OverflowNegInfinity); }

                        // Detect overflow by reversing the shift-and-add process
                        if is_positive && (prev_sig != (sig - digit as f64) / radix as f64)
                            { return Err(ParseNumberError::OverflowInfinity); }
                        if !is_positive && (prev_sig != (sig + digit as f64) / radix as f64)
                            { return Err(ParseNumberError::OverflowNegInfinity); }
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
            for (i, &c) in cs.by_ref() {
                if settings.allow_underscore && c == '_' { continue; }
                match to_digit(c) {
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
                            { return Err(ParseNumberError::OverflowInfinity); }
                        if !is_positive && sig > prev_sig
                            { return Err(ParseNumberError::OverflowNegInfinity); }
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
                    Some(('-', src)) => (false, parse_u64(settings, src)),
                    Some(('+', src)) => (true,  parse_u64(settings, src)),
                    Some((_, _))     => (true,  parse_u64(settings, src)),
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
}

/// Contains errors when parsing a string.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ParseStringError {
    /// Expected four hexadecimals, found less characters
    ExpectedFourHexadecimals,
    /// Expected character `0-9a-fA-F`
    ExpectedHexadecimal,
    /// Found four hexadecimals, but not an invalid unicode character
    ExpectedValidUnicode,
    /// A character escape `\x` is invalid
    ExpectedValidEscapeCharacter,
}

impl Display for ParseStringError {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FormatError> {
        match self {
            &ParseStringError::ExpectedFourHexadecimals =>
                fmt.write_str("Expected four hexadecimals xxxx 0-9A-F"),
            &ParseStringError::ExpectedHexadecimal =>
                fmt.write_str("Expected hexadecimal 0-9A-F"),
            &ParseStringError::ExpectedValidUnicode =>
                fmt.write_str("Expected valid unicode"),
            &ParseStringError::ExpectedValidEscapeCharacter =>
                fmt.write_str("Expected valid escape character '\"\\/bfnrtu'"),
        }
    }
}

/// The settings for reading numbers.
#[derive(Copy, Clone, Debug)]
pub struct NumberSettings {
    /// Whether to allow underscore in number.
    pub allow_underscore: bool,
}

/// Error when parsing number.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ParseNumberError {
    /// The number was empty.
    ExpectedDigits,
    /// The number is of invalid format.
    Invalid,
    /// The number overflowed to infinity.
    OverflowInfinity,
    /// The number overflowed to negative infinity.
    OverflowNegInfinity,
}

impl Display for ParseNumberError {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), FormatError> {
        match self {
            &ParseNumberError::ExpectedDigits =>
                fmt.write_str("Expected digits"),
            &ParseNumberError::Invalid =>
                fmt.write_str("Expected valid number format, for example `20.3e-4`"),
            &ParseNumberError::OverflowInfinity =>
                fmt.write_str("Number overflowed toward positive infinity"),
            &ParseNumberError::OverflowNegInfinity =>
                fmt.write_str("Number overflowed toward negative infinity"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use range::Range;

    #[test]
    pub fn test_token() {
        let text = "one day, a nice day".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).tag("one");
        assert_eq!(res, Some(Range::new(0, 3)));
        let res = ReadToken::new(&text, 0).tag("two");
        assert_eq!(res, None);

        let text = "°a".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).tag("°a");
        assert_eq!(res, Some(Range::new(0, 2)));
    }

    #[test]
    pub fn test_until_any_or_whitespace() {
        let text = "one day, a nice day".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).until_any_or_whitespace(",");
        assert_eq!(res, (Range::new(0, 3), None));
        let res = ReadToken::new(&text[3..], 3).until_any_or_whitespace(",");
        assert_eq!(res, (Range::empty(3), None));
        let res = ReadToken::new(&text[4..], 4).until_any_or_whitespace(",");
        assert_eq!(res, (Range::new(4, 3), Some(0)));
    }

    #[test]
    pub fn test_until_any() {
        let text = "one day, a nice day".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).until_any(",");
        assert_eq!(res, (Range::new(0, 7), Some(0)));
        let res = ReadToken::new(&text[3..], 3).until_any(",");
        assert_eq!(res, (Range::new(3, 4), Some(0)));
        let res = ReadToken::new(&text[8..], 8).until_any(",");
        assert_eq!(res, (Range::new(8, 11), None));
    }

    #[test]
    pub fn test_whitespace() {
        let text = "   123".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).whitespace();
        assert_eq!(res, Range::new(0, 3));
    }

    #[test]
    pub fn test_string() {
        let text = "\"hello\"".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, Some(Range::new(0, 7)));
        let txt = ReadToken::new(&text, 0).parse_string(res.unwrap().length);
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "hello");

        let text = "\"he\\\"llo\"".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, Some(Range::new(0, 9)));
        let txt = ReadToken::new(&text, 0).parse_string(res.unwrap().length);
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "he\"llo");

        let text = "\"he\"llo\"".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, Some(Range::new(0, 4)));
        let txt = ReadToken::new(&text, 0).parse_string(res.unwrap().length);
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "he");

        let text = "\"hello\\\"".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, None);
    }

    #[test]
    pub fn test_number() {
        let settings = NumberSettings { allow_underscore: false };

        let to_chars = |s: &str| s.chars().collect::<Vec<char>>();

        let chars = to_chars("20");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 20.0);
        let chars = to_chars("-20");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, -20.0);
        let chars = to_chars("2e2");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2e2);
        let chars = to_chars("2.5");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2.5);
        let res: f64 = "2.5e2".parse().unwrap();
        assert_eq!(res, 2.5e2);
        let chars = to_chars("2.5E2");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2.5E2);
        let chars = to_chars("2.5E-2");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2.5E-2);

        let text = "20".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 2)));

        let text = "-20".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2e2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5e2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E-2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 6)));
    }

    #[test]
    pub fn test_underscore_number() {
        let settings = NumberSettings { allow_underscore: true };

        let to_chars = |s: &str| s.chars().collect::<Vec<char>>();

        let chars = to_chars("2_0");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 20.0);
        let chars = to_chars("-2_0");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, -20.0);
        let chars = to_chars("2_e2_");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2e2);
        let chars = to_chars("2_.5_");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2.5);
        let chars = to_chars("2_.5_e2_");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2.5e2);
        let chars = to_chars("2_.5_E2_");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2.5E2);
        let chars = to_chars("2_.5_E-2_");
        let res: f64 = ReadToken::new(&chars, 0)
            .parse_number(&settings, chars.len()).unwrap();
        assert_eq!(res, 2.5E-2);

        let text = "20".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 2)));

        let text = "-20".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2e2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5e2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E-2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 6)));

        let text = "_2.5E-2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, None);

        let text = "2_.5E-2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 7)));

        let text = "2_000_000.5E-2".chars().collect::<Vec<char>>();
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 14)));
    }
}
