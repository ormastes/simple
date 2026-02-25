use crate::token::{NumericSuffix, TokenKind};

impl<'a> super::Lexer<'a> {
    /// Helper to check if underscore is followed by a unit suffix (not a digit separator).
    /// Takes a validator to check if a character is a valid digit for the current radix.
    #[inline]
    fn is_unit_suffix_start_with_validator<F>(&mut self, is_valid_digit: &F) -> bool
    where
        F: Fn(char) -> bool,
    {
        let mut peek_ahead = self.chars.clone();
        peek_ahead.next(); // skip '_'
        if let Some((_, next)) = peek_ahead.next() {
            // It's a unit suffix only if it's alphabetic AND not a valid digit for current radix
            // This handles hex numbers where 'a'-'f' are valid digits, not unit suffixes
            next.is_alphabetic() && !is_valid_digit(next)
        } else {
            false
        }
    }

    /// Helper to scan digits for a given radix, handling underscores and unit suffixes.
    fn scan_radix_digits<F>(&mut self, num_str: &mut String, is_valid_digit: F) -> bool
    where
        F: Fn(char) -> bool,
    {
        let mut found_digits = false;
        while let Some(c) = self.peek() {
            if is_valid_digit(c) {
                num_str.push(c);
                self.advance();
                found_digits = true;
            } else if c == '_' {
                if self.is_unit_suffix_start_with_validator(&is_valid_digit) {
                    break; // Unit suffix detected
                }
                self.advance(); // Skip digit separator
            } else {
                break;
            }
        }
        found_digits
    }

    /// Helper to parse integers with non-decimal radix
    fn parse_radix_integer(&mut self, num_str: &str, radix: u32, radix_name: &str) -> TokenKind {
        let digits = &num_str[2..].replace('_', "");
        match u64::from_str_radix(digits, radix) {
            Ok(n) => {
                let n = n as i64;
                if let Some(suffix) = self.scan_numeric_suffix() {
                    TokenKind::TypedInteger(n, suffix)
                } else {
                    TokenKind::Integer(n)
                }
            }
            Err(_) => {
                TokenKind::Error(format!("Invalid {} number: {}", radix_name, num_str))
            }
        }
    }

    pub(super) fn scan_number(&mut self, first: char) -> TokenKind {
        let mut num_str = String::from(first);
        let mut is_float = false;

        // Handle hex, octal, binary
        if first == '0' {
            if let Some(ch) = self.peek() {
                match ch {
                    'x' | 'X' => {
                        self.advance();
                        num_str.push(ch);
                        self.scan_radix_digits(&mut num_str, |c| c.is_ascii_hexdigit());
                        // Use u64 parsing to handle full range of hex values (including 0x8000... and 0xFFFF...)
                        // then reinterpret as i64 bit pattern
                        let hex_digits = &num_str[2..].replace('_', "");
                        return match u64::from_str_radix(hex_digits, 16) {
                            Ok(n) => {
                                let n = n as i64;
                                if let Some(suffix) = self.scan_numeric_suffix() {
                                    TokenKind::TypedInteger(n, suffix)
                                } else {
                                    TokenKind::Integer(n)
                                }
                            }
                            Err(_) => TokenKind::Error(format!("Invalid hex number: {}", num_str)),
                        };
                    }
                    'o' | 'O' => {
                        self.advance();
                        num_str.push(ch);
                        self.scan_radix_digits(&mut num_str, |c| ('0'..='7').contains(&c));
                        return self.parse_radix_integer(&num_str, 8, "octal");
                    }
                    'b' | 'B' => {
                        self.advance();
                        num_str.push(ch);
                        self.scan_radix_digits(&mut num_str, |c| c == '0' || c == '1');
                        return self.parse_radix_integer(&num_str, 2, "binary");
                    }
                    _ => {}
                }
            }
        }

        // Regular decimal number
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                num_str.push(ch);
                self.advance();
            } else if ch == '_' {
                // Look ahead: if underscore is followed by letter (unit suffix), stop
                let mut peek_ahead = self.chars.clone();
                peek_ahead.next(); // skip '_'
                if let Some((_, next)) = peek_ahead.next() {
                    if next.is_alphabetic() {
                        // This is a unit suffix like _km, stop number parsing
                        break;
                    }
                }
                // Otherwise it's a digit separator, consume and skip
                self.advance();
            } else {
                break;
            }
        }

        // Check for float
        if self.check('.') {
            // Look ahead to distinguish 1.2 from 1..2
            let mut peek_iter = self.chars.clone();
            peek_iter.next(); // skip '.'
            let peek_next = peek_iter.next();
            if let Some((_, next_ch)) = peek_next {
                if next_ch.is_ascii_digit() {
                    is_float = true;
                    self.advance(); // consume '.'
                    num_str.push('.');

                    while let Some(ch) = self.peek() {
                        if ch.is_ascii_digit() {
                            num_str.push(ch);
                            self.advance();
                        } else if ch == '_' {
                            // Look ahead: if underscore is followed by letter (unit suffix), stop
                            let mut peek_ahead = self.chars.clone();
                            peek_ahead.next(); // skip '_'
                            if let Some((_, next)) = peek_ahead.next() {
                                if next.is_alphabetic() {
                                    break;
                                }
                            }
                            self.advance();
                        } else {
                            break;
                        }
                    }
                } else if next_ch == '\n' || next_ch == '\r' || next_ch == ' ' || next_ch == '\t'
                    || next_ch == ')' || next_ch == ']' || next_ch == '}' || next_ch == '#' {
                    // `5.` followed by whitespace/newline/closing bracket/comment
                    // but NOT comma (could be tuple field like `result.0,`)
                    // and NOT alphanumeric (could be method call like `5.to_string()`)
                    // Treat as float `5.0`
                    is_float = true;
                    self.advance(); // consume '.'
                    num_str.push('.');
                    num_str.push('0');
                }
            } else {
                // `5.` at EOF - treat as float 5.0
                is_float = true;
                self.advance(); // consume '.'
                num_str.push('.');
                num_str.push('0');
            }
        }

        // Check for exponent
        if let Some(ch) = self.peek() {
            if ch == 'e' || ch == 'E' {
                is_float = true;
                self.advance();
                num_str.push(ch);

                if let Some(sign) = self.peek() {
                    if sign == '+' || sign == '-' {
                        self.advance();
                        num_str.push(sign);
                    }
                }

                while let Some(c) = self.peek() {
                    if c.is_ascii_digit() {
                        num_str.push(c);
                        self.advance();
                    } else {
                        break;
                    }
                }
            }
        }

        // Check for type suffix
        let suffix = self.scan_numeric_suffix();

        if is_float {
            match num_str.parse::<f64>() {
                Ok(n) => {
                    if let Some(s) = suffix {
                        TokenKind::TypedFloat(n, s)
                    } else {
                        TokenKind::Float(n)
                    }
                }
                Err(_) => TokenKind::Error(format!("Invalid float: {}", num_str)),
            }
        } else {
            match num_str.parse::<i64>() {
                Ok(n) => {
                    if let Some(s) = suffix {
                        TokenKind::TypedInteger(n, s)
                    } else {
                        TokenKind::Integer(n)
                    }
                }
                Err(_) => {
                    // Try parsing as u64 for large unsigned values, store as i64
                    // (overflow wraps, but at least the parser doesn't fail)
                    match num_str.parse::<u64>() {
                        Ok(n) => {
                            let wrapped = n as i64;
                            if let Some(s) = suffix {
                                TokenKind::TypedInteger(wrapped, s)
                            } else {
                                TokenKind::Integer(wrapped)
                            }
                        }
                        Err(_) => {
                            // For truly huge numbers, clamp to i64::MAX
                            if let Some(s) = suffix {
                                TokenKind::TypedInteger(i64::MAX, s)
                            } else {
                                TokenKind::Integer(i64::MAX)
                            }
                        }
                    }
                }
            }
        }
    }

    pub(super) fn scan_numeric_suffix(&mut self) -> Option<NumericSuffix> {
        // Check for type suffix: i8, i16, i32, i64, u8, u16, u32, u64, f32, f64
        // Or user-defined unit suffix starting with _ like _km, _hr
        let mut suffix = String::new();

        // Peek ahead to see if we have a suffix
        let mut peek_iter = self.chars.clone();
        if let Some((_, ch)) = peek_iter.peek() {
            if *ch == 'i' || *ch == 'u' || *ch == 'f' || *ch == '_' {
                // Collect the suffix
                while let Some(&(_, c)) = peek_iter.peek() {
                    if c.is_alphanumeric() || c == '_' {
                        suffix.push(c);
                        peek_iter.next();
                    } else {
                        break;
                    }
                }
            }
        }

        // Check if it's a valid suffix
        let result = match suffix.as_str() {
            "i8" => Some(NumericSuffix::I8),
            "i16" => Some(NumericSuffix::I16),
            "i32" => Some(NumericSuffix::I32),
            "i64" => Some(NumericSuffix::I64),
            "u8" => Some(NumericSuffix::U8),
            "u16" => Some(NumericSuffix::U16),
            "u32" => Some(NumericSuffix::U32),
            "u64" => Some(NumericSuffix::U64),
            "f32" => Some(NumericSuffix::F32),
            "f64" => Some(NumericSuffix::F64),
            s if s.starts_with('_') && s.len() > 1 => {
                // User-defined unit suffix (e.g., _km, _hr)
                Some(NumericSuffix::Unit(s[1..].to_string()))
            }
            _ => None,
        };

        // Actually consume the suffix if valid
        if result.is_some() {
            for _ in 0..suffix.len() {
                self.advance();
            }
        }

        result
    }

}
