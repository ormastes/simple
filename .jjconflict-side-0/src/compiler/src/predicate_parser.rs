//! Parser for unified predicate expressions.
//!
//! Parses pc{...} predicate syntax into unified Predicate AST.
//! Supports: !, &, |, (), and various selector functions.

use crate::predicate::{ArgPatterns, Predicate, Selector, SignaturePattern};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Not,         // !
    And,         // &
    Or,          // |
    LParen,      // (
    RParen,      // )
    Comma,       // ,
    Selector(String, Vec<String>), // name(arg1, arg2, ...)
}

/// Parse a predicate expression from string.
///
/// Accepts both:
/// - `pc{ ... }` syntax (strips the wrapper)
/// - Raw predicate expression
pub fn parse_predicate(input: &str) -> Result<Predicate, String> {
    let trimmed = input.trim();
    let inner = if trimmed.starts_with("pc{") && trimmed.ends_with('}') {
        trimmed[3..trimmed.len() - 1].trim()
    } else {
        trimmed
    };

    let tokens = tokenize(inner)?;
    let mut parser = Parser::new(tokens);
    let expr = parser.parse_expr()?;

    if parser.pos < parser.tokens.len() {
        return Err("unexpected trailing tokens in predicate".to_string());
    }

    Ok(expr)
}

fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut chars = input.chars().peekable();
    let mut tokens = Vec::new();

    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\n' | '\r' => {
                chars.next();
            }
            '!' => {
                chars.next();
                tokens.push(Token::Not);
            }
            '&' => {
                chars.next();
                tokens.push(Token::And);
            }
            '|' => {
                chars.next();
                tokens.push(Token::Or);
            }
            '(' => {
                chars.next();
                tokens.push(Token::LParen);
            }
            ')' => {
                chars.next();
                tokens.push(Token::RParen);
            }
            ',' => {
                chars.next();
                tokens.push(Token::Comma);
            }
            _ if c.is_ascii_alphabetic() || c == '_' => {
                // Parse selector name
                let mut name = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_ascii_alphanumeric() || ch == '_' {
                        name.push(ch);
                        chars.next();
                    } else {
                        break;
                    }
                }

                // Skip whitespace
                while let Some(&ch) = chars.peek() {
                    if ch.is_ascii_whitespace() {
                        chars.next();
                    } else {
                        break;
                    }
                }

                // Expect '('
                if chars.peek() != Some(&'(') {
                    return Err(format!("expected '(' after selector '{}'", name));
                }
                chars.next();

                // Parse arguments (comma-separated)
                let args = parse_selector_args(&mut chars)?;

                tokens.push(Token::Selector(name, args));
            }
            _ => {
                return Err(format!("unexpected character '{}' in predicate", c));
            }
        }
    }

    Ok(tokens)
}

fn parse_selector_args(chars: &mut std::iter::Peekable<std::str::Chars>) -> Result<Vec<String>, String> {
    let mut args = Vec::new();
    let mut current_arg = String::new();
    let mut depth = 0;

    loop {
        match chars.peek() {
            None => return Err("unclosed selector argument list".to_string()),
            Some(&')') if depth == 0 => {
                chars.next();
                if !current_arg.trim().is_empty() {
                    args.push(current_arg.trim().to_string());
                }
                break;
            }
            Some(&'(') => {
                depth += 1;
                current_arg.push('(');
                chars.next();
            }
            Some(&')') => {
                depth -= 1;
                current_arg.push(')');
                chars.next();
            }
            Some(&',') if depth == 0 => {
                chars.next();
                if !current_arg.trim().is_empty() {
                    args.push(current_arg.trim().to_string());
                    current_arg.clear();
                }
            }
            Some(&ch) => {
                current_arg.push(ch);
                chars.next();
            }
        }
    }

    Ok(args)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn parse_expr(&mut self) -> Result<Predicate, String> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Predicate, String> {
        let mut expr = self.parse_and()?;
        while matches!(self.peek_token(), Some(Token::Or)) {
            self.pos += 1;
            let rhs = self.parse_and()?;
            expr = Predicate::Or(Box::new(expr), Box::new(rhs));
        }
        Ok(expr)
    }

    fn parse_and(&mut self) -> Result<Predicate, String> {
        let mut expr = self.parse_not()?;
        while matches!(self.peek_token(), Some(Token::And)) {
            self.pos += 1;
            let rhs = self.parse_not()?;
            expr = Predicate::And(Box::new(expr), Box::new(rhs));
        }
        Ok(expr)
    }

    fn parse_not(&mut self) -> Result<Predicate, String> {
        if matches!(self.peek_token(), Some(Token::Not)) {
            self.pos += 1;
            let inner = self.parse_not()?;
            return Ok(Predicate::Not(Box::new(inner)));
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<Predicate, String> {
        if matches!(self.peek_token(), Some(Token::LParen)) {
            self.pos += 1;
            let expr = self.parse_expr()?;
            if !matches!(self.peek_token(), Some(Token::RParen)) {
                return Err("expected ')'".to_string());
            }
            self.pos += 1;
            return Ok(expr);
        }

        if let Some(Token::Selector(name, args)) = self.peek_token().cloned() {
            self.pos += 1;
            let selector = self.parse_selector(&name, &args)?;
            return Ok(Predicate::Selector(selector));
        }

        Err("expected selector or '('".to_string())
    }

    fn parse_selector(&self, name: &str, args: &[String]) -> Result<Selector, String> {
        match name {
            // Weaving selectors
            "execution" => {
                if args.len() != 1 {
                    return Err(format!("execution() expects 1 argument, got {}", args.len()));
                }
                let sig_pattern = parse_signature_pattern(&args[0])?;
                Ok(Selector::Execution(sig_pattern))
            }
            "within" => {
                if args.len() != 1 {
                    return Err(format!("within() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Within(args[0].clone()))
            }
            "attr" => {
                if args.len() != 1 {
                    return Err(format!("attr() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Attr(args[0].clone()))
            }
            "effect" => {
                if args.len() != 1 {
                    return Err(format!("effect() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Effect(args[0].clone()))
            }
            "test" => {
                if args.len() != 1 {
                    return Err(format!("test() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Test(args[0].clone()))
            }
            "decision" => {
                if !args.is_empty() {
                    return Err(format!("decision() expects 0 arguments, got {}", args.len()));
                }
                Ok(Selector::Decision)
            }
            "condition" => {
                if !args.is_empty() {
                    return Err(format!("condition() expects 0 arguments, got {}", args.len()));
                }
                Ok(Selector::Condition)
            }
            "call" => {
                if args.len() != 1 {
                    return Err(format!("call() expects 1 argument, got {}", args.len()));
                }
                let sig_pattern = parse_signature_pattern(&args[0])?;
                Ok(Selector::Call(sig_pattern))
            }

            // DI selectors
            "type" => {
                if args.len() != 1 {
                    return Err(format!("type() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Type(args[0].clone()))
            }

            // Runtime AOP selectors
            "init" => {
                if args.len() != 1 {
                    return Err(format!("init() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Init(args[0].clone()))
            }

            // Architecture selectors
            "import" => {
                if args.len() != 2 {
                    return Err(format!("import() expects 2 arguments, got {}", args.len()));
                }
                Ok(Selector::Import {
                    from: args[0].clone(),
                    to: args[1].clone(),
                })
            }
            "depend" => {
                if args.len() != 2 {
                    return Err(format!("depend() expects 2 arguments, got {}", args.len()));
                }
                Ok(Selector::Depend {
                    from: args[0].clone(),
                    to: args[1].clone(),
                })
            }
            "use" => {
                if args.len() != 1 {
                    return Err(format!("use() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Use(args[0].clone()))
            }
            "export" => {
                if args.len() != 1 {
                    return Err(format!("export() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Export(args[0].clone()))
            }
            "config" => {
                if args.len() != 1 {
                    return Err(format!("config() expects 1 argument, got {}", args.len()));
                }
                Ok(Selector::Config(args[0].clone()))
            }

            _ => Err(format!("unknown selector '{}'", name)),
        }
    }

    fn peek_token(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }
}

/// Parse signature pattern: `ret_type qname(args)`
///
/// Examples:
/// - `* User.new(..)`
/// - `i64 *.calculate(i64, i64)`
/// - `void Logger.log(*)`
fn parse_signature_pattern(input: &str) -> Result<SignaturePattern, String> {
    let trimmed = input.trim();

    // Find the opening parenthesis
    let paren_pos = trimmed.find('(')
        .ok_or_else(|| format!("invalid signature pattern '{}': missing '('", trimmed))?;

    if !trimmed.ends_with(')') {
        return Err(format!("invalid signature pattern '{}': missing closing ')'", trimmed));
    }

    // Extract arguments (between parentheses)
    let args_str = &trimmed[paren_pos + 1..trimmed.len() - 1].trim();
    let args = if args_str.is_empty() {
        ArgPatterns::Specific(vec![])
    } else if *args_str == ".." {
        ArgPatterns::Any
    } else {
        let arg_list: Vec<String> = args_str
            .split(',')
            .map(|s| s.trim().to_string())
            .collect();
        ArgPatterns::Specific(arg_list)
    };

    // Extract return type and qualified name (before parentheses)
    let before_paren = &trimmed[..paren_pos].trim();
    let parts: Vec<&str> = before_paren.split_whitespace().collect();

    if parts.is_empty() {
        return Err(format!("invalid signature pattern '{}': missing function name", trimmed));
    }

    let (return_type, qualified_name) = if parts.len() == 1 {
        // No return type specified, default to *
        ("*".to_string(), parts[0].to_string())
    } else if parts.len() == 2 {
        (parts[0].to_string(), parts[1].to_string())
    } else {
        return Err(format!("invalid signature pattern '{}': too many parts", trimmed));
    };

    Ok(SignaturePattern {
        return_type,
        qualified_name,
        args,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_selector() {
        let pred = parse_predicate("pc{ type(Foo) }").unwrap();
        match pred {
            Predicate::Selector(Selector::Type(pattern)) => {
                assert_eq!(pattern, "Foo");
            }
            _ => panic!("expected Type selector"),
        }
    }

    #[test]
    fn test_parse_combinators() {
        let pred = parse_predicate("pc{ type(Foo) & attr(inject) }").unwrap();
        match pred {
            Predicate::And(_, _) => {}
            _ => panic!("expected And predicate"),
        }
    }

    #[test]
    fn test_parse_negation() {
        let pred = parse_predicate("pc{ !attr(test) }").unwrap();
        match pred {
            Predicate::Not(_) => {}
            _ => panic!("expected Not predicate"),
        }
    }

    #[test]
    fn test_parse_signature_pattern() {
        let sig = parse_signature_pattern("* User.new(..)").unwrap();
        assert_eq!(sig.return_type, "*");
        assert_eq!(sig.qualified_name, "User.new");
        assert!(matches!(sig.args, ArgPatterns::Any));

        let sig2 = parse_signature_pattern("i64 *.calculate(i64, i64)").unwrap();
        assert_eq!(sig2.return_type, "i64");
        assert_eq!(sig2.qualified_name, "*.calculate");
        match sig2.args {
            ArgPatterns::Specific(args) => {
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], "i64");
                assert_eq!(args[1], "i64");
            }
            _ => panic!("expected specific args"),
        }
    }

    #[test]
    fn test_parse_execution_selector() {
        let pred = parse_predicate("pc{ execution(* User.new(..)) }").unwrap();
        match pred {
            Predicate::Selector(Selector::Execution(sig)) => {
                assert_eq!(sig.qualified_name, "User.new");
            }
            _ => panic!("expected Execution selector"),
        }
    }

    #[test]
    fn test_parse_architecture_selectors() {
        let pred = parse_predicate("pc{ import(domain.**, infrastructure.**) }").unwrap();
        match pred {
            Predicate::Selector(Selector::Import { from, to }) => {
                assert_eq!(from, "domain.**");
                assert_eq!(to, "infrastructure.**");
            }
            _ => panic!("expected Import selector"),
        }
    }

    #[test]
    fn test_parse_complex_expression() {
        let pred = parse_predicate(
            "pc{ (type(User*) | type(*Service)) & !attr(test) }"
        ).unwrap();

        // Should be And(Or(Type, Type), Not(Attr))
        match pred {
            Predicate::And(lhs, rhs) => {
                assert!(matches!(*lhs, Predicate::Or(_, _)));
                assert!(matches!(*rhs, Predicate::Not(_)));
            }
            _ => panic!("expected And at top level"),
        }
    }
}
