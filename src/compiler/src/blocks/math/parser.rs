//! Math expression parser.
//!
//! Parses math expressions using operator precedence parsing:
//! 1. Comparison: = != < <= > >= ≈
//! 2. Additive: + -
//! 3. Multiplicative: * / % (and implicit multiplication)
//! 4. Power: ^ (right-associative)
//! 5. Unary: - (negation)
//! 6. Postfix: subscript[i], function(args)
//! 7. Primary: numbers, identifiers, grouping

use super::ast::{MathExpr, Range};
use super::lexer::{MathLexer, MathToken};
use crate::error::CompileError;

/// Parse math expression
pub fn parse_math(input: &str) -> Result<(MathExpr, Vec<String>), CompileError> {
    let lexer = MathLexer::new(input);
    let (tokens, warnings) = lexer.tokenize();
    let mut parser = MathParser::new(tokens, warnings);
    let expr = parser.parse_expression()?;
    Ok((expr, parser.warnings))
}

/// Math expression parser
struct MathParser {
    tokens: Vec<MathToken>,
    pos: usize,
    warnings: Vec<String>,
}

impl MathParser {
    fn new(tokens: Vec<MathToken>, warnings: Vec<String>) -> Self {
        Self {
            tokens,
            pos: 0,
            warnings,
        }
    }

    fn current(&self) -> &MathToken {
        self.tokens.get(self.pos).unwrap_or(&MathToken::Eof)
    }

    fn peek(&self) -> &MathToken {
        self.tokens.get(self.pos + 1).unwrap_or(&MathToken::Eof)
    }

    fn advance(&mut self) -> &MathToken {
        let tok = self.current().clone();
        self.pos += 1;
        self.tokens.get(self.pos - 1).unwrap_or(&MathToken::Eof)
    }

    fn expect(&mut self, expected: MathToken) -> Result<(), CompileError> {
        if self.current() == &expected {
            self.advance();
            Ok(())
        } else {
            Err(CompileError::Semantic(format!(
                "expected {:?}, found {:?}",
                expected,
                self.current()
            )))
        }
    }

    /// Parse complete expression
    fn parse_expression(&mut self) -> Result<MathExpr, CompileError> {
        self.parse_comparison()
    }

    /// Parse comparison: a = b, a < b, etc.
    fn parse_comparison(&mut self) -> Result<MathExpr, CompileError> {
        let mut left = self.parse_additive()?;

        loop {
            match self.current() {
                MathToken::Eq => {
                    self.advance();
                    let right = self.parse_additive()?;
                    left = MathExpr::Eq(Box::new(left), Box::new(right));
                }
                MathToken::Neq => {
                    self.advance();
                    let right = self.parse_additive()?;
                    left = MathExpr::Neq(Box::new(left), Box::new(right));
                }
                MathToken::Lt => {
                    self.advance();
                    let right = self.parse_additive()?;
                    left = MathExpr::Lt(Box::new(left), Box::new(right));
                }
                MathToken::Le => {
                    self.advance();
                    let right = self.parse_additive()?;
                    left = MathExpr::Le(Box::new(left), Box::new(right));
                }
                MathToken::Gt => {
                    self.advance();
                    let right = self.parse_additive()?;
                    left = MathExpr::Gt(Box::new(left), Box::new(right));
                }
                MathToken::Ge => {
                    self.advance();
                    let right = self.parse_additive()?;
                    left = MathExpr::Ge(Box::new(left), Box::new(right));
                }
                MathToken::Approx => {
                    self.advance();
                    let right = self.parse_additive()?;
                    left = MathExpr::Approx(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }

        Ok(left)
    }

    /// Parse additive: a + b, a - b
    fn parse_additive(&mut self) -> Result<MathExpr, CompileError> {
        let mut left = self.parse_multiplicative()?;

        loop {
            match self.current() {
                MathToken::Plus => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = MathExpr::Add(Box::new(left), Box::new(right));
                }
                MathToken::Minus => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    left = MathExpr::Sub(Box::new(left), Box::new(right));
                }
                MathToken::PlusMinus => {
                    self.advance();
                    let right = self.parse_multiplicative()?;
                    // ± is typically used for +/- notation, store as special
                    // For evaluation, we'll just use Add (could also support both)
                    left = MathExpr::Add(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }

        Ok(left)
    }

    /// Parse multiplicative: a * b, a / b, a % b
    fn parse_multiplicative(&mut self) -> Result<MathExpr, CompileError> {
        let mut left = self.parse_power()?;

        loop {
            match self.current() {
                MathToken::Star => {
                    self.advance();
                    let right = self.parse_power()?;
                    left = MathExpr::Mul(Box::new(left), Box::new(right));
                }
                MathToken::Slash => {
                    self.advance();
                    let right = self.parse_power()?;
                    left = MathExpr::Div(Box::new(left), Box::new(right));
                }
                MathToken::Percent => {
                    self.advance();
                    let right = self.parse_power()?;
                    left = MathExpr::Mod(Box::new(left), Box::new(right));
                }
                // Implicit multiplication: number followed by identifier or paren
                // e.g., 2x, 3(x+1)
                MathToken::Ident(_) | MathToken::LParen if self.is_implicit_mul(&left) => {
                    let right = self.parse_power()?;
                    left = MathExpr::Mul(Box::new(left), Box::new(right));
                }
                _ => break,
            }
        }

        Ok(left)
    }

    /// Check if implicit multiplication should apply
    fn is_implicit_mul(&self, left: &MathExpr) -> bool {
        matches!(
            left,
            MathExpr::Int(_)
                | MathExpr::Float(_)
                | MathExpr::Var(_)
                | MathExpr::Group(_)
                | MathExpr::Subscript(_, _)
        )
    }

    /// Parse power: a ^ b (right-associative)
    fn parse_power(&mut self) -> Result<MathExpr, CompileError> {
        let left = self.parse_unary()?;

        if self.current() == &MathToken::Caret {
            self.advance();
            let right = self.parse_power()?; // Right-associative
            return Ok(MathExpr::Pow(Box::new(left), Box::new(right)));
        }

        Ok(left)
    }

    /// Parse unary: -x
    fn parse_unary(&mut self) -> Result<MathExpr, CompileError> {
        if self.current() == &MathToken::Minus {
            self.advance();
            let expr = self.parse_unary()?;
            return Ok(MathExpr::Neg(Box::new(expr)));
        }

        self.parse_postfix()
    }

    /// Parse postfix: subscript[i], function(args)
    fn parse_postfix(&mut self) -> Result<MathExpr, CompileError> {
        let mut expr = self.parse_primary()?;

        loop {
            match self.current() {
                // Subscript: x[i]
                MathToken::LBracket => {
                    self.advance();
                    let index = self.parse_expression()?;
                    self.expect(MathToken::RBracket)?;
                    expr = MathExpr::Subscript(Box::new(expr), Box::new(index));
                }
                // LaTeX-style subscript: x_i or x_{expr}
                MathToken::Underscore => {
                    self.advance();
                    let index = if self.current() == &MathToken::LBrace {
                        self.advance();
                        let idx = self.parse_expression()?;
                        self.expect(MathToken::RBrace)?;
                        idx
                    } else {
                        // Single token subscript
                        self.parse_primary()?
                    };
                    self.warnings.push(
                        "subscript syntax `x_i` is deprecated, use `x[i]` instead".to_string(),
                    );
                    expr = MathExpr::Subscript(Box::new(expr), Box::new(index));
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    /// Parse primary: numbers, identifiers, groups, function calls
    fn parse_primary(&mut self) -> Result<MathExpr, CompileError> {
        match self.current().clone() {
            MathToken::Int(n) => {
                self.advance();
                Ok(MathExpr::Int(n))
            }
            MathToken::Float(f) => {
                self.advance();
                Ok(MathExpr::Float(f))
            }
            MathToken::Ident(name) => {
                self.advance();
                // Check if followed by ( for function call
                if self.current() == &MathToken::LParen {
                    self.parse_function_call(name)
                } else {
                    Ok(MathExpr::Var(name))
                }
            }
            MathToken::LatexCmd(cmd) => {
                self.advance();
                self.parse_latex_command(cmd)
            }
            MathToken::LParen => {
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(MathToken::RParen)?;
                Ok(MathExpr::Group(Box::new(expr)))
            }
            MathToken::Pipe => {
                // Absolute value: |x|
                self.advance();
                let expr = self.parse_expression()?;
                self.expect(MathToken::Pipe)?;
                Ok(MathExpr::Abs(Box::new(expr)))
            }
            _ => Err(CompileError::Semantic(format!(
                "unexpected token in math: {:?}",
                self.current()
            ))),
        }
    }

    /// Parse function call: f(args) or binder(var, range) body
    fn parse_function_call(&mut self, name: String) -> Result<MathExpr, CompileError> {
        self.expect(MathToken::LParen)?;

        // Check for binders: sum, prod, int
        if matches!(name.as_str(), "sum" | "prod" | "int") {
            return self.parse_binder(name);
        }

        // Regular function call
        let mut args = Vec::new();

        if self.current() != &MathToken::RParen {
            args.push(self.parse_expression()?);

            while self.current() == &MathToken::Comma {
                self.advance();
                args.push(self.parse_expression()?);
            }
        }

        self.expect(MathToken::RParen)?;

        Ok(MathExpr::App(name, args))
    }

    /// Parse binder: sum(i, 1..n) expr
    fn parse_binder(&mut self, name: String) -> Result<MathExpr, CompileError> {
        // Parse variable name
        let var = match self.current().clone() {
            MathToken::Ident(v) => {
                self.advance();
                v
            }
            _ => {
                return Err(CompileError::Semantic(
                    "expected variable name in binder".to_string(),
                ))
            }
        };

        // Optional type annotation (ignored for now)
        if self.current() == &MathToken::Colon {
            self.advance();
            // Skip type
            let _ = self.parse_primary()?;
        }

        self.expect(MathToken::Comma)?;

        // Parse range: a..b
        let start = self.parse_expression()?;
        self.expect(MathToken::DotDot)?;
        let end = self.parse_expression()?;

        self.expect(MathToken::RParen)?;

        // Parse body expression
        let body = self.parse_multiplicative()?;

        let range = Box::new(Range::new(start, end));

        match name.as_str() {
            "sum" => Ok(MathExpr::Sum {
                var,
                range,
                body: Box::new(body),
            }),
            "prod" => Ok(MathExpr::Prod {
                var,
                range,
                body: Box::new(body),
            }),
            "int" => {
                // For integrals, handle optional "dx" suffix
                // Skip if present
                if let MathToken::Ident(dx) = self.current() {
                    if dx.starts_with('d') {
                        self.advance();
                    }
                }
                Ok(MathExpr::Int {
                    var,
                    range,
                    body: Box::new(body),
                })
            }
            _ => unreachable!(),
        }
    }

    /// Parse LaTeX command (compatibility mode)
    fn parse_latex_command(&mut self, cmd: String) -> Result<MathExpr, CompileError> {
        match cmd.as_str() {
            // \frac{a}{b} -> frac(a, b)
            "frac" => {
                self.expect(MathToken::LBrace)?;
                let num = self.parse_expression()?;
                self.expect(MathToken::RBrace)?;
                self.expect(MathToken::LBrace)?;
                let denom = self.parse_expression()?;
                self.expect(MathToken::RBrace)?;
                Ok(MathExpr::App("frac".to_string(), vec![num, denom]))
            }
            // \sqrt{x} -> sqrt(x)
            "sqrt" => {
                self.expect(MathToken::LBrace)?;
                let arg = self.parse_expression()?;
                self.expect(MathToken::RBrace)?;
                Ok(MathExpr::App("sqrt".to_string(), vec![arg]))
            }
            // \sum_{i=a}^{b} -> sum(i, a..b)
            "sum" | "prod" | "int" => self.parse_latex_binder(cmd),
            // Greek letters: \alpha -> alpha
            name if is_greek_letter(name) => Ok(MathExpr::Var(name)),
            // \cdot, \times -> multiplication
            "cdot" | "times" => {
                // These are binary operators, but in LaTeX they appear between operands
                // Return a placeholder that will be handled by the caller
                Err(CompileError::Semantic(format!(
                    "LaTeX operator \\{} should be replaced with *",
                    cmd
                )))
            }
            // \pm -> ±
            "pm" => Ok(MathExpr::Var("pm".to_string())),
            // \left, \right - grouping hints, ignore
            "left" | "right" => {
                // Skip the following delimiter
                self.advance();
                self.parse_expression()
            }
            _ => {
                // Unknown LaTeX command, treat as identifier
                self.warnings.push(format!("unknown LaTeX command: \\{}", cmd));
                Ok(MathExpr::Var(cmd))
            }
        }
    }

    /// Parse LaTeX-style binder: \sum_{i=a}^{b} expr
    fn parse_latex_binder(&mut self, cmd: String) -> Result<MathExpr, CompileError> {
        // \sum_{i=a}^{b} or \sum_{i=a}^b
        self.expect(MathToken::Underscore)?;

        let (var, start) = if self.current() == &MathToken::LBrace {
            self.advance();
            // i=a inside braces
            let var = match self.current().clone() {
                MathToken::Ident(v) => {
                    self.advance();
                    v
                }
                _ => {
                    return Err(CompileError::Semantic(
                        "expected variable in binder".to_string(),
                    ))
                }
            };
            self.expect(MathToken::Eq)?;
            let start = self.parse_expression()?;
            self.expect(MathToken::RBrace)?;
            (var, start)
        } else {
            // Single token: i=a
            let var = match self.current().clone() {
                MathToken::Ident(v) => {
                    self.advance();
                    v
                }
                _ => {
                    return Err(CompileError::Semantic(
                        "expected variable in binder".to_string(),
                    ))
                }
            };
            self.expect(MathToken::Eq)?;
            let start = self.parse_primary()?;
            (var, start)
        };

        // ^{b} or ^b
        self.expect(MathToken::Caret)?;

        let end = if self.current() == &MathToken::LBrace {
            self.advance();
            let e = self.parse_expression()?;
            self.expect(MathToken::RBrace)?;
            e
        } else {
            self.parse_primary()?
        };

        // Parse body
        let body = self.parse_multiplicative()?;

        let range = Box::new(Range::new(start, end));

        match cmd.as_str() {
            "sum" => Ok(MathExpr::Sum {
                var,
                range,
                body: Box::new(body),
            }),
            "prod" => Ok(MathExpr::Prod {
                var,
                range,
                body: Box::new(body),
            }),
            "int" => {
                // Skip "dx" if present
                if let MathToken::Ident(dx) = self.current() {
                    if dx.starts_with('d') {
                        self.advance();
                    }
                }
                Ok(MathExpr::Int {
                    var,
                    range,
                    body: Box::new(body),
                })
            }
            _ => unreachable!(),
        }
    }
}

/// Check if name is a Greek letter
fn is_greek_letter(name: &str) -> bool {
    matches!(
        name,
        "alpha"
            | "beta"
            | "gamma"
            | "delta"
            | "epsilon"
            | "zeta"
            | "eta"
            | "theta"
            | "iota"
            | "kappa"
            | "lambda"
            | "mu"
            | "nu"
            | "xi"
            | "omicron"
            | "pi"
            | "rho"
            | "sigma"
            | "tau"
            | "upsilon"
            | "phi"
            | "chi"
            | "psi"
            | "omega"
            | "Alpha"
            | "Beta"
            | "Gamma"
            | "Delta"
            | "Epsilon"
            | "Zeta"
            | "Eta"
            | "Theta"
            | "Iota"
            | "Kappa"
            | "Lambda"
            | "Mu"
            | "Nu"
            | "Xi"
            | "Omicron"
            | "Pi"
            | "Rho"
            | "Sigma"
            | "Tau"
            | "Upsilon"
            | "Phi"
            | "Chi"
            | "Psi"
            | "Omega"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_integer() {
        let (expr, _) = parse_math("42").unwrap();
        assert_eq!(expr, MathExpr::Int(42));
    }

    #[test]
    fn test_parse_addition() {
        let (expr, _) = parse_math("1 + 2").unwrap();
        assert_eq!(
            expr,
            MathExpr::Add(Box::new(MathExpr::Int(1)), Box::new(MathExpr::Int(2)))
        );
    }

    #[test]
    fn test_parse_multiplication() {
        let (expr, _) = parse_math("2 * 3").unwrap();
        assert_eq!(
            expr,
            MathExpr::Mul(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)))
        );
    }

    #[test]
    fn test_parse_power() {
        let (expr, _) = parse_math("2^3").unwrap();
        assert_eq!(
            expr,
            MathExpr::Pow(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)))
        );
    }

    #[test]
    fn test_parse_function() {
        let (expr, _) = parse_math("sqrt(16)").unwrap();
        assert_eq!(
            expr,
            MathExpr::App("sqrt".to_string(), vec![MathExpr::Int(16)])
        );
    }

    #[test]
    fn test_parse_frac_function() {
        let (expr, _) = parse_math("frac(1, 2)").unwrap();
        assert_eq!(
            expr,
            MathExpr::App("frac".to_string(), vec![MathExpr::Int(1), MathExpr::Int(2)])
        );
    }

    #[test]
    fn test_parse_variable() {
        let (expr, _) = parse_math("pi").unwrap();
        assert_eq!(expr, MathExpr::Var("pi".to_string()));
    }

    #[test]
    fn test_parse_latex_frac() {
        let (expr, warnings) = parse_math("\\frac{1}{2}").unwrap();
        assert_eq!(
            expr,
            MathExpr::App("frac".to_string(), vec![MathExpr::Int(1), MathExpr::Int(2)])
        );
        assert!(!warnings.is_empty()); // Should warn about LaTeX syntax
    }

    #[test]
    fn test_parse_grouping() {
        let (expr, _) = parse_math("(1 + 2) * 3").unwrap();
        match expr {
            MathExpr::Mul(left, right) => {
                assert!(matches!(*left, MathExpr::Group(_)));
                assert_eq!(*right, MathExpr::Int(3));
            }
            _ => panic!("expected multiplication"),
        }
    }

    #[test]
    fn test_parse_subscript() {
        let (expr, _) = parse_math("x[i]").unwrap();
        assert_eq!(
            expr,
            MathExpr::Subscript(
                Box::new(MathExpr::Var("x".to_string())),
                Box::new(MathExpr::Var("i".to_string()))
            )
        );
    }

    #[test]
    fn test_parse_absolute() {
        let (expr, _) = parse_math("|x|").unwrap();
        assert_eq!(
            expr,
            MathExpr::Abs(Box::new(MathExpr::Var("x".to_string())))
        );
    }
}
