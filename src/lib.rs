#![deny(missing_docs)]

//! A simple library to read tokens using look ahead

extern crate range;

use std::fmt::{ Display, Formatter };
use std::fmt::Error as FormatError;
use range::Range;

/// Stores the state of parsing.
#[derive(Copy, Clone, Debug)]
pub struct ReadToken<'a> {
    src: &'a str,
    offset: usize,
}

impl<'a> ReadToken<'a> {
    /// Creates a new `ReadToken`.
    /// The offset is in characters.
    pub fn new(src: &'a str, offset: usize) -> ReadToken<'a> {
        ReadToken {
            src: src,
            offset: offset,
        }
    }

    /// Consumes n characters.
    pub fn consume(self, n: usize) -> ReadToken<'a> {
        let n = self.src.chars().take(n)
            .map(|c| c.len_utf8()).fold(0, |a, b| a + b);
        ReadToken {
            src: &self.src[n..],
            offset: self.offset + n
        }
    }

    /// Reads a raw string.
    pub fn raw_string(&self, n: usize) -> String {
        self.src.chars().take(n).collect::<String>()
    }

    /// Returns whether a range of characters ended with newline character
    /// followed by whitespace.
    fn ended_with_newline(&self, range: Range) -> bool {
        let end = range.next_offset() - self.offset;
        let mut ends_with_newline = false;
        for c in self.src.chars().take(end) {
            if c as char == '\n' {
                ends_with_newline = true;
            } else if !c.is_whitespace() {
                ends_with_newline = false;
            }
        }
        ends_with_newline
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
            let mut ended_with_newline = false;
            let mut reached_end = true;
            let mut len = 0;
            let mut byte_offset = 0;
            for (i, c) in read_token.src.char_indices() {
                if c == '\n' {
                    ended_with_newline = true;
                    reached_end = false;
                    break;
                }
                if !c.is_whitespace() {
                    reached_end = false;
                    break;
                }
                len += 1;
                byte_offset = i;
            }
            if reached_end {
                read_token.offset += len;
                break;
            } else if ended_with_newline {
                read_token.src = &read_token.src[byte_offset + 1..];
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
                            read_token = read_token.consume(range.length);
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
        if self.src.starts_with(tag) {
            Some(self.peek(tag.chars().count()))
        } else {
            None
        }
    }

    /// Reads a token until any character in string or whitespace.
    /// Returns `(range, None)` if stopping at whitespace
    /// or end of characters.
    /// Returns `(range, Some(x))` if stopping at a character.
    pub fn until_any_or_whitespace(&self, any: &str) -> (Range, Option<usize>) {
        for (i, c) in self.src.chars().enumerate() {
            if c.is_whitespace() { return (self.peek(i), None) }
            for (j, b) in any.chars().enumerate() {
                if c == b { return (self.peek(i), Some(j)) }
            }
        }
        (self.peek(self.src.chars().count()), None)
    }

    /// Reads token until any character in string.
    /// Returns `(new_state, range, None)` if stopping at end of characters.
    /// Returns `(new_state, range, Some(x))` if stopping at a character.
    pub fn until_any(&self, any: &str) -> (Range, Option<usize>) {
        for (i, c) in self.src.chars().enumerate() {
            for (j, b) in any.chars().enumerate() {
                if c == b { return (self.peek(i), Some(j)) }
            }
        }
        (self.peek(self.src.chars().count()), None)
    }

    /// Reads whitespace.
    pub fn whitespace(&self) -> Range {
        for (i, c) in self.src.chars().enumerate() {
            if !c.is_whitespace() { return self.peek(i); }
        }
        self.peek(self.src.chars().count())
    }

    /// Reads string with character escapes.
    pub fn string(&self) -> Option<Range> {
        let mut chars = self.src.chars();
        match chars.next() {
            None => { return None; }
            Some('"') => {}
            _ => { return None; }
        }
        let mut escape = false;
        for (i, c) in chars.enumerate() {
            if c == '\\' { escape = true; continue; }
            if !escape && c == '"' {
                return Some(self.peek(i + 2))
            }
            if escape { escape = false; }
        }
        None
    }

    /// Reads number.
    pub fn number(&self, settings: &NumberSettings) -> Option<Range> {
        let mut has_sign = false;
        let mut has_decimal_separator = false;
        let mut has_scientific = false;
        let mut has_exponent_sign = false;
        let mut has_digit = false;
        for (i, c) in self.src.chars().enumerate() {
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
        if self.src.len() > 0 { Some(self.peek(self.src.chars().count())) }
        else { None }
    }

    /// Parses four unicode characters in hexadecimal format.
    fn parse_unicode(&self) -> Result<char, Range<ParseStringError>> {
        use std::char;

        let mut u: [u32; 4] = [0; 4];
        let mut chars = self.src.chars();
        for (i, c) in u.iter_mut().enumerate() {
            let ch = match chars.next() {
                None => {
                    return Err(Range::new(self.offset, self.src.len())
                        .wrap(ParseStringError::ExpectedFourHexadecimals));
                }
                Some(ch) => ch
            };
            match ch.to_digit(16) {
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
        let mut skip_unicode = 0;
        for (i, (j, c)) in self.src.char_indices()
            .skip(1).take(length).enumerate() {
            if skip_unicode > 0 {
                skip_unicode -= 1;
                continue;
            }
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
                        match ReadToken::new(&self.src[j + 1..], offset)
                            .parse_unicode() {
                            Ok(x) => { skip_unicode = 4; x },
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
        fn slice_shift_char(src: &str) -> Option<(char, &str)> {
            if src.len() == 0 { None }
            else {
                let ch = src.chars().next().unwrap();
                Some((ch, &src[ch.len_utf8()..]))
            }
        }

        #[inline(always)]
        fn parse_u64(settings: &NumberSettings, src: &str) -> Result<u64, ()> {
            let mut res: u64 = 0;
            for c in src.chars() {
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
        let n = self.src.chars().take(n)
            .map(|c| c.len_utf8()).fold(0, |a, b| a + b);
        let src = &self.src[..n];
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
        let mut cs = src.chars().enumerate();
        // Exponent prefix and exponent index offset
        let mut exp_info = None::<(char, usize)>;

        // Parse the integer part of the significand
        for (i, c) in cs.by_ref() {
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
            for (i, c) in cs.by_ref() {
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
        let text = "one day, a nice day";
        let res = ReadToken::new(&text, 0).tag("one");
        assert_eq!(res, Some(Range::new(0, 3)));
        let res = ReadToken::new(&text, 0).tag("two");
        assert_eq!(res, None);

        let text = "°a";
        let res = ReadToken::new(&text, 0).tag("°a");
        assert_eq!(res, Some(Range::new(0, 2)));
    }

    #[test]
    pub fn test_until_any_or_whitespace() {
        let text = "one day, a nice day";
        let res = ReadToken::new(&text, 0).until_any_or_whitespace(",");
        assert_eq!(res, (Range::new(0, 3), None));
        let res = ReadToken::new(&text[3..], 3).until_any_or_whitespace(",");
        assert_eq!(res, (Range::empty(3), None));
        let res = ReadToken::new(&text[4..], 4).until_any_or_whitespace(",");
        assert_eq!(res, (Range::new(4, 3), Some(0)));
    }

    #[test]
    pub fn test_until_any() {
        let text = "one day, a nice day";
        let res = ReadToken::new(&text, 0).until_any(",");
        assert_eq!(res, (Range::new(0, 7), Some(0)));
        let res = ReadToken::new(&text[3..], 3).until_any(",");
        assert_eq!(res, (Range::new(3, 4), Some(0)));
        let res = ReadToken::new(&text[8..], 8).until_any(",");
        assert_eq!(res, (Range::new(8, 11), None));
    }

    #[test]
    pub fn test_whitespace() {
        let text = "   123";
        let res = ReadToken::new(&text, 0).whitespace();
        assert_eq!(res, Range::new(0, 3));
    }

    #[test]
    pub fn test_string() {
        let text = "\"hello\"";
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, Some(Range::new(0, 7)));
        let txt = ReadToken::new(&text, 0).parse_string(res.unwrap().length);
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "hello");

        let text = "\"he\\\"llo\"";
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, Some(Range::new(0, 9)));
        let txt = ReadToken::new(&text, 0).parse_string(res.unwrap().length);
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "he\"llo");

        let text = "\"he\"llo\"";
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, Some(Range::new(0, 4)));
        let txt = ReadToken::new(&text, 0).parse_string(res.unwrap().length);
        let txt = txt.ok().unwrap();
        assert_eq!(txt, "he");

        let text = "\"\\u20AC\"";
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, Some(Range::new(0, 8)));
        let txt = ReadToken::new(&text, 0).parse_string(res.unwrap().length);
        let txt = txt.unwrap();
        assert_eq!(txt, "€");

        let text = "\"😎\"";
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, Some(Range::new(0, 3)));
        let txt = ReadToken::new(&text, 0).parse_string(res.unwrap().length);
        let txt = txt.unwrap();
        assert_eq!(txt, "😎");

        let text = "\"hello\\\"";
        let res = ReadToken::new(&text, 0).string();
        assert_eq!(res, None);
    }

    #[test]
    pub fn test_number() {
        let settings = NumberSettings { allow_underscore: false };

        let text = "20";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 20.0);
        let text = "-20";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, -20.0);
        let text = "2e2";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2e2);
        let text = "2.5";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2.5);
        let res: f64 = "2.5e2".parse().unwrap();
        assert_eq!(res, 2.5e2);
        let text = "2.5E2";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2.5E2);
        let text = "2.5E-2";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2.5E-2);

        let text = "20";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 2)));

        let text = "-20";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2e2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5e2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E-2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 6)));
    }

    #[test]
    pub fn test_underscore_number() {
        let settings = NumberSettings { allow_underscore: true };

        let text = "2_0";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 20.0);
        let text = "-2_0";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, -20.0);
        let text = "2_e2_";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2e2);
        let text = "2_.5_";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2.5);
        let text = "2_.5_e2_";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2.5e2);
        let text = "2_.5_E2_";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2.5E2);
        let text = "2_.5_E-2_";
        let res: f64 = ReadToken::new(&text, 0)
            .parse_number(&settings, text.chars().count()).unwrap();
        assert_eq!(res, 2.5E-2);

        let text = "20";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 2)));

        let text = "-20";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2e2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 3)));

        let text = "2.5e2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 5)));

        let text = "2.5E-2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 6)));

        let text = "_2.5E-2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, None);

        let text = "2_.5E-2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 7)));

        let text = "2_000_000.5E-2";
        let res = ReadToken::new(&text, 0).number(&settings);
        assert_eq!(res, Some(Range::new(0, 14)));
    }
}
