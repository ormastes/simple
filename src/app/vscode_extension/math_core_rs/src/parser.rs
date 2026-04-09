use std::fmt::Write;

#[derive(Debug, Clone)]
pub enum Expr {
    Number(String),
    Ident(String),
    UnaryNeg(Box<Expr>),
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Call {
        name: String,
        args: Vec<Expr>,
    },
    Group(Box<Expr>),
    Subscript {
        base: Box<Expr>,
        sub: Box<Expr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Number(String),
    Ident(String),
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    Underscore,
    LParen,
    RParen,
    Comma,
    Eof,
}

pub fn parse_expression(source: &str) -> Result<Expr, String> {
    let mut parser = Parser::new(source);
    let expr = parser.parse_expr()?;
    if parser.peek() != Token::Eof {
        return Err(format!(
            "unexpected trailing token: {}",
            parser.peek_display()
        ));
    }
    Ok(expr)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(source: &str) -> Self {
        Self {
            tokens: lex(source),
            pos: 0,
        }
    }

    fn peek(&self) -> Token {
        self.tokens.get(self.pos).cloned().unwrap_or(Token::Eof)
    }

    fn peek_display(&self) -> String {
        match self.peek() {
            Token::Number(n) => format!("number({n})"),
            Token::Ident(s) => format!("ident({s})"),
            Token::Plus => "+".to_string(),
            Token::Minus => "-".to_string(),
            Token::Star => "*".to_string(),
            Token::Slash => "/".to_string(),
            Token::Caret => "^".to_string(),
            Token::Underscore => "_".to_string(),
            Token::LParen => "(".to_string(),
            Token::RParen => ")".to_string(),
            Token::Comma => ",".to_string(),
            Token::Eof => "eof".to_string(),
        }
    }

    fn bump(&mut self) {
        self.pos += 1;
    }

    fn eat(&mut self, expected: Token) -> Result<(), String> {
        if self.peek() == expected {
            self.bump();
            Ok(())
        } else {
            Err(format!(
                "expected {:?}, found {}",
                expected,
                self.peek_display()
            ))
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, String> {
        self.parse_add_sub()
    }

    fn parse_add_sub(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_mul_div()?;
        loop {
            let op = match self.peek() {
                Token::Plus => BinOp::Add,
                Token::Minus => BinOp::Sub,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_mul_div()?;
            expr = Expr::Binary {
                op,
                left: Box::new(expr),
                right: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_mul_div(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_power()?;
        loop {
            let op = match self.peek() {
                Token::Star => BinOp::Mul,
                Token::Slash => BinOp::Div,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_power()?;
            expr = Expr::Binary {
                op,
                left: Box::new(expr),
                right: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_power(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_unary()?;
        if self.peek() == Token::Caret {
            self.bump();
            let rhs = self.parse_power()?;
            expr = Expr::Binary {
                op: BinOp::Pow,
                left: Box::new(expr),
                right: Box::new(rhs),
            };
        }
        Ok(expr)
    }

    fn parse_unary(&mut self) -> Result<Expr, String> {
        if self.peek() == Token::Minus {
            self.bump();
            Ok(Expr::UnaryNeg(Box::new(self.parse_unary()?)))
        } else {
            self.parse_postfix()
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_primary()?;
        loop {
            match self.peek() {
                Token::Underscore => {
                    self.bump();
                    let sub = self.parse_postfix_atom()?;
                    expr = Expr::Subscript {
                        base: Box::new(expr),
                        sub: Box::new(sub),
                    };
                }
                Token::LParen => {
                    if let Expr::Ident(name) = expr {
                        let args = self.parse_call_args()?;
                        expr = Expr::Call { name, args };
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn parse_postfix_atom(&mut self) -> Result<Expr, String> {
        match self.peek() {
            Token::LParen => {
                self.bump();
                let inner = self.parse_expr()?;
                self.eat(Token::RParen)?;
                Ok(Expr::Group(Box::new(inner)))
            }
            _ => self.parse_primary(),
        }
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>, String> {
        self.eat(Token::LParen)?;
        let mut args = Vec::new();
        if self.peek() == Token::RParen {
            self.bump();
            return Ok(args);
        }
        loop {
            args.push(self.parse_expr()?);
            match self.peek() {
                Token::Comma => {
                    self.bump();
                }
                Token::RParen => {
                    self.bump();
                    break;
                }
                _ => {
                    return Err(format!(
                        "expected `,` or `)`, found {}",
                        self.peek_display()
                    ))
                }
            }
        }
        Ok(args)
    }

    fn parse_primary(&mut self) -> Result<Expr, String> {
        match self.peek() {
            Token::Number(n) => {
                self.bump();
                Ok(Expr::Number(n))
            }
            Token::Ident(name) => {
                self.bump();
                if self.peek() == Token::LParen {
                    let args = self.parse_call_args()?;
                    Ok(Expr::Call { name, args })
                } else {
                    Ok(Expr::Ident(name))
                }
            }
            Token::LParen => {
                self.bump();
                let expr = self.parse_expr()?;
                self.eat(Token::RParen)?;
                Ok(Expr::Group(Box::new(expr)))
            }
            Token::Eof => Err("unexpected end of input".to_string()),
            _ => Err(format!("unexpected token {}", self.peek_display())),
        }
    }
}

fn lex(source: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = source.chars().collect();
    let mut i = 0usize;

    while i < chars.len() {
        let ch = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }

        if ch.is_ascii_digit()
            || (ch == '.' && i + 1 < chars.len() && chars[i + 1].is_ascii_digit())
        {
            let start = i;
            i += 1;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '.') {
                i += 1;
            }
            tokens.push(Token::Number(chars[start..i].iter().collect()));
            continue;
        }

        if is_ident_start(ch) {
            let start = i;
            i += 1;
            while i < chars.len() && is_ident_continue(chars[i]) {
                i += 1;
            }
            tokens.push(Token::Ident(chars[start..i].iter().collect()));
            continue;
        }

        match ch {
            '+' => tokens.push(Token::Plus),
            '-' => tokens.push(Token::Minus),
            '*' => tokens.push(Token::Star),
            '/' => tokens.push(Token::Slash),
            '^' => tokens.push(Token::Caret),
            '_' => tokens.push(Token::Underscore),
            '(' => tokens.push(Token::LParen),
            ')' => tokens.push(Token::RParen),
            ',' => tokens.push(Token::Comma),
            _ => {}
        }
        i += 1;
    }

    tokens.push(Token::Eof);
    tokens
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic()
}

fn is_ident_continue(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

pub fn debug_tree(expr: &Expr) -> String {
    match expr {
        Expr::Number(n) => format!("Number({n})"),
        Expr::Ident(s) => format!("Ident({s})"),
        Expr::UnaryNeg(expr) => format!("Neg({})", debug_tree(expr)),
        Expr::Binary { op, left, right } => {
            let op = match op {
                BinOp::Add => "Add",
                BinOp::Sub => "Sub",
                BinOp::Mul => "Mul",
                BinOp::Div => "Div",
                BinOp::Pow => "Pow",
            };
            format!("{op}({}, {})", debug_tree(left), debug_tree(right))
        }
        Expr::Call { name, args } => {
            let mut out = String::new();
            let _ = write!(&mut out, "Call({name}");
            for arg in args {
                let _ = write!(&mut out, ", {}", debug_tree(arg));
            }
            out.push(')');
            out
        }
        Expr::Group(expr) => format!("Group({})", debug_tree(expr)),
        Expr::Subscript { base, sub } => {
            format!("Subscript({}, {})", debug_tree(base), debug_tree(sub))
        }
    }
}
