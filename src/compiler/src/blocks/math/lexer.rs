//! Math expression lexer.
//!
//! Tokenizes math expressions with support for:
//! - Numbers (integer and float)
//! - Identifiers (variables, constants, Greek letters)
//! - Operators (+, -, *, /, ^, etc.)
//! - Unicode math symbols (√, π, α, ∑, etc.)
//! - LaTeX compatibility (\frac, \sqrt, etc.) with warnings

use std::iter::Peekable;
use std::str::Chars;

/// Math token
#[derive(Debug, Clone, PartialEq)]
pub enum MathToken {
    // Literals
    Int(i64),
    Float(f64),

    // Identifiers and keywords
    Ident(String),

    // LaTeX command (compatibility, will warn)
    LatexCmd(String), // e.g., "frac" from \frac

    // Operators
    Plus,      // +
    Minus,     // -
    Star,      // *
    Slash,     // /
    Caret,     // ^
    Percent,   // %
    PlusMinus, // ± or +-

    // Comparison
    Eq,     // =
    Neq,    // != or ≠
    Lt,     // <
    Le,     // <= or ≤
    Gt,     // >
    Ge,     // >= or ≥
    Approx, // ≈

    // Grouping
    LParen,   // (
    RParen,   // )
    LBracket, // [
    RBracket, // ]
    LBrace,   // {
    RBrace,   // }
    Pipe,     // |

    // Punctuation
    Comma,  // ,
    Colon,  // :
    Dot,    // .
    DotDot, // ..
    Semi,   // ;

    // Special
    Underscore, // _

    // End of input
    Eof,
}

/// Lexer for math expressions
pub struct MathLexer<'a> {
    chars: Peekable<Chars<'a>>,
    pub warnings: Vec<String>,
}

impl<'a> MathLexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
            warnings: Vec::new(),
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    fn advance(&mut self) -> Option<char> {
        self.chars.next()
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn scan_number(&mut self, first: char) -> MathToken {
        let mut num_str = String::from(first);
        let mut is_float = false;

        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                num_str.push(ch);
                self.advance();
            } else if ch == '.' && !is_float {
                // Check if next char is also a digit (to distinguish from ..)
                let mut chars_clone = self.chars.clone();
                chars_clone.next(); // skip '.'
                if let Some(next) = chars_clone.next() {
                    if next.is_ascii_digit() {
                        is_float = true;
                        num_str.push(ch);
                        self.advance();
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        if is_float {
            MathToken::Float(num_str.parse().unwrap_or(0.0))
        } else {
            MathToken::Int(num_str.parse().unwrap_or(0))
        }
    }

    fn scan_identifier(&mut self, first: char) -> MathToken {
        let mut name = String::from(first);

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                name.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        MathToken::Ident(name)
    }

    fn scan_latex_command(&mut self) -> MathToken {
        // Skip the backslash, already consumed
        let mut name = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_alphabetic() {
                name.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        if name.is_empty() {
            // Just a backslash, treat as error or special
            MathToken::Ident("\\".to_string())
        } else {
            // Emit warning for LaTeX syntax
            let simple_equiv = latex_to_simple(&name);
            self.warnings.push(format!(
                "LaTeX syntax `\\{}` is deprecated, use `{}` instead",
                name, simple_equiv
            ));
            MathToken::LatexCmd(name)
        }
    }

    pub fn next_token(&mut self) -> MathToken {
        self.skip_whitespace();

        match self.advance() {
            None => MathToken::Eof,
            Some(ch) => match ch {
                // Numbers
                '0'..='9' => self.scan_number(ch),

                // Identifiers (including Greek Unicode)
                'a'..='z' | 'A'..='Z' | '_' => self.scan_identifier(ch),

                // Unicode Greek letters as identifiers
                'α'..='ω' | 'Α'..='Ω' | 'π' | 'τ' | 'φ' | 'ψ' => {
                    // Map Unicode Greek to ASCII name
                    let name = unicode_greek_to_name(ch);
                    MathToken::Ident(name.to_string())
                }

                // Unicode math symbols
                '√' => MathToken::Ident("sqrt".to_string()),
                '∑' => MathToken::Ident("sum".to_string()),
                '∏' => MathToken::Ident("prod".to_string()),
                '∫' => MathToken::Ident("int".to_string()),
                '∞' => MathToken::Ident("inf".to_string()),
                '±' => MathToken::PlusMinus,
                '≠' => MathToken::Neq,
                '≤' => MathToken::Le,
                '≥' => MathToken::Ge,
                '≈' => MathToken::Approx,
                '·' => MathToken::Star, // Middle dot as multiplication

                // LaTeX commands
                '\\' => self.scan_latex_command(),

                // Operators
                '+' => {
                    if self.peek() == Some('-') {
                        self.advance();
                        MathToken::PlusMinus
                    } else {
                        MathToken::Plus
                    }
                }
                '-' => MathToken::Minus,
                '*' => MathToken::Star,
                '/' => MathToken::Slash,
                '^' => MathToken::Caret,
                '%' => MathToken::Percent,

                // Comparison
                '=' => MathToken::Eq,
                '!' => {
                    if self.peek() == Some('=') {
                        self.advance();
                        MathToken::Neq
                    } else {
                        // Factorial might use ! but we handle it differently
                        MathToken::Ident("factorial".to_string())
                    }
                }
                '<' => {
                    if self.peek() == Some('=') {
                        self.advance();
                        MathToken::Le
                    } else {
                        MathToken::Lt
                    }
                }
                '>' => {
                    if self.peek() == Some('=') {
                        self.advance();
                        MathToken::Ge
                    } else {
                        MathToken::Gt
                    }
                }

                // Grouping
                '(' => MathToken::LParen,
                ')' => MathToken::RParen,
                '[' => MathToken::LBracket,
                ']' => MathToken::RBracket,
                '{' => MathToken::LBrace,
                '}' => MathToken::RBrace,
                '|' => MathToken::Pipe,

                // Punctuation
                ',' => MathToken::Comma,
                ':' => MathToken::Colon,
                '.' => {
                    if self.peek() == Some('.') {
                        self.advance();
                        MathToken::DotDot
                    } else {
                        MathToken::Dot
                    }
                }
                ';' => MathToken::Semi,
                '_' => MathToken::Underscore,

                // Unknown character - try as identifier start
                _ if ch.is_alphabetic() => self.scan_identifier(ch),
                _ => {
                    self.warnings.push(format!("unknown character in math: '{}'", ch));
                    self.next_token() // Skip and continue
                }
            },
        }
    }

    /// Tokenize the entire input
    pub fn tokenize(mut self) -> (Vec<MathToken>, Vec<String>) {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            if tok == MathToken::Eof {
                tokens.push(tok);
                break;
            }
            tokens.push(tok);
        }
        (tokens, self.warnings)
    }
}

/// Map Unicode Greek letter to ASCII name
fn unicode_greek_to_name(ch: char) -> &'static str {
    match ch {
        'α' => "alpha",
        'β' => "beta",
        'γ' => "gamma",
        'δ' => "delta",
        'ε' => "epsilon",
        'ζ' => "zeta",
        'η' => "eta",
        'θ' => "theta",
        'ι' => "iota",
        'κ' => "kappa",
        'λ' => "lambda",
        'μ' => "mu",
        'ν' => "nu",
        'ξ' => "xi",
        'ο' => "omicron",
        'π' => "pi",
        'ρ' => "rho",
        'σ' => "sigma",
        'τ' => "tau",
        'υ' => "upsilon",
        'φ' => "phi",
        'χ' => "chi",
        'ψ' => "psi",
        'ω' => "omega",
        // Uppercase
        'Α' => "Alpha",
        'Β' => "Beta",
        'Γ' => "Gamma",
        'Δ' => "Delta",
        'Ε' => "Epsilon",
        'Ζ' => "Zeta",
        'Η' => "Eta",
        'Θ' => "Theta",
        'Ι' => "Iota",
        'Κ' => "Kappa",
        'Λ' => "Lambda",
        'Μ' => "Mu",
        'Ν' => "Nu",
        'Ξ' => "Xi",
        'Ο' => "Omicron",
        'Π' => "Pi",
        'Ρ' => "Rho",
        'Σ' => "Sigma",
        'Τ' => "Tau",
        'Υ' => "Upsilon",
        'Φ' => "Phi",
        'Χ' => "Chi",
        'Ψ' => "Psi",
        'Ω' => "Omega",
        _ => "unknown",
    }
}

/// Map LaTeX command to Simple equivalent (for warning messages)
fn latex_to_simple(cmd: &str) -> String {
    match cmd {
        "frac" => "frac(a, b)".to_string(),
        "sqrt" => "sqrt(x)".to_string(),
        "sum" => "sum(i, a..b) expr".to_string(),
        "prod" => "prod(i, a..b) expr".to_string(),
        "int" => "int(x, a..b) expr dx".to_string(),
        "alpha" => "alpha".to_string(),
        "beta" => "beta".to_string(),
        "gamma" => "gamma".to_string(),
        "delta" => "delta".to_string(),
        "epsilon" => "epsilon".to_string(),
        "pi" => "pi".to_string(),
        "tau" => "tau".to_string(),
        "phi" => "phi".to_string(),
        "theta" => "theta".to_string(),
        "omega" => "omega".to_string(),
        "cdot" => "*".to_string(),
        "times" => "*".to_string(),
        "pm" => "±".to_string(),
        "left" => "(grouping ignored)".to_string(),
        "right" => "(grouping ignored)".to_string(),
        _ => cmd.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenize_number() {
        let lexer = MathLexer::new("42");
        let (tokens, _) = lexer.tokenize();
        assert_eq!(tokens[0], MathToken::Int(42));
    }

    #[test]
    fn test_tokenize_float() {
        let lexer = MathLexer::new("3.14");
        let (tokens, _) = lexer.tokenize();
        assert_eq!(tokens[0], MathToken::Float(3.14));
    }

    #[test]
    fn test_tokenize_identifier() {
        let lexer = MathLexer::new("alpha");
        let (tokens, _) = lexer.tokenize();
        assert_eq!(tokens[0], MathToken::Ident("alpha".to_string()));
    }

    #[test]
    fn test_tokenize_operators() {
        let lexer = MathLexer::new("+ - * / ^");
        let (tokens, _) = lexer.tokenize();
        assert_eq!(tokens[0], MathToken::Plus);
        assert_eq!(tokens[1], MathToken::Minus);
        assert_eq!(tokens[2], MathToken::Star);
        assert_eq!(tokens[3], MathToken::Slash);
        assert_eq!(tokens[4], MathToken::Caret);
    }

    #[test]
    fn test_tokenize_latex_warns() {
        let lexer = MathLexer::new("\\pi");
        let (tokens, warnings) = lexer.tokenize();
        assert_eq!(tokens[0], MathToken::LatexCmd("pi".to_string()));
        assert!(!warnings.is_empty());
    }

    #[test]
    fn test_tokenize_unicode_greek() {
        let lexer = MathLexer::new("π");
        let (tokens, _) = lexer.tokenize();
        assert_eq!(tokens[0], MathToken::Ident("pi".to_string()));
    }

    #[test]
    fn test_tokenize_range() {
        let lexer = MathLexer::new("1..10");
        let (tokens, _) = lexer.tokenize();
        assert_eq!(tokens[0], MathToken::Int(1));
        assert_eq!(tokens[1], MathToken::DotDot);
        assert_eq!(tokens[2], MathToken::Int(10));
    }
}
