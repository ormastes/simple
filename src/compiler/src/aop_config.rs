//! Runtime AOP configuration parsing for interpreter-only around init support.

#[derive(Debug, Clone)]
pub struct AopConfig {
    pub runtime_enabled: bool,
    pub around: Vec<AopAroundRule>,
}

#[derive(Debug, Clone)]
pub struct AopAroundRule {
    pub predicate: AopPredicate,
    pub advice: String,
    pub priority: i64,
    pub order: usize,
    pub raw_predicate: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AopSelector {
    Init(String),
    Within(String),
    Attr(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AopPredicate {
    Selector(AopSelector),
    Not(Box<AopPredicate>),
    And(Box<AopPredicate>, Box<AopPredicate>),
    Or(Box<AopPredicate>, Box<AopPredicate>),
}

#[derive(Debug, Clone)]
pub struct AopMatchContext<'a> {
    pub type_name: &'a str,
    pub module_path: &'a str,
    pub attrs: &'a [String],
}

impl AopPredicate {
    pub fn matches(&self, ctx: &AopMatchContext<'_>) -> bool {
        match self {
            AopPredicate::Selector(sel) => match sel {
                AopSelector::Init(pattern) => match_pattern(pattern, ctx.type_name),
                AopSelector::Within(pattern) => match_pattern(pattern, ctx.module_path),
                AopSelector::Attr(name) => ctx.attrs.iter().any(|attr| attr == name),
            },
            AopPredicate::Not(inner) => !inner.matches(ctx),
            AopPredicate::And(lhs, rhs) => lhs.matches(ctx) && rhs.matches(ctx),
            AopPredicate::Or(lhs, rhs) => lhs.matches(ctx) || rhs.matches(ctx),
        }
    }

    pub fn specificity(&self) -> i32 {
        match self {
            AopPredicate::Selector(sel) => selector_specificity(sel),
            AopPredicate::Not(inner) => inner.specificity() - 1,
            AopPredicate::And(lhs, rhs) => lhs.specificity() + rhs.specificity(),
            AopPredicate::Or(lhs, rhs) => lhs.specificity().max(rhs.specificity()),
        }
    }
}

fn selector_specificity(sel: &AopSelector) -> i32 {
    match sel {
        AopSelector::Attr(_) => 2,
        AopSelector::Init(pattern) | AopSelector::Within(pattern) => {
            pattern
                .split('.')
                .map(segment_specificity)
                .sum::<i32>()
        }
    }
}

fn segment_specificity(segment: &str) -> i32 {
    if segment == "**" {
        -2
    } else if segment == "*" {
        0
    } else if segment.contains('*') {
        1
    } else {
        2
    }
}

fn match_pattern(pattern: &str, value: &str) -> bool {
    let pat_segments: Vec<&str> = pattern.split('.').collect();
    let val_segments: Vec<&str> = value.split('.').collect();
    match_segments(&pat_segments, &val_segments)
}

fn match_segments(pat: &[&str], val: &[&str]) -> bool {
    if pat.is_empty() {
        return val.is_empty();
    }
    if pat[0] == "**" {
        for skip in 0..=val.len() {
            if match_segments(&pat[1..], &val[skip..]) {
                return true;
            }
        }
        return false;
    }
    if val.is_empty() {
        return false;
    }
    if !match_segment(pat[0], val[0]) {
        return false;
    }
    match_segments(&pat[1..], &val[1..])
}

fn match_segment(pattern: &str, value: &str) -> bool {
    if pattern == "*" {
        return true;
    }
    if !pattern.contains('*') {
        return pattern == value;
    }

    let mut remainder = value;
    let mut is_first = true;
    for part in pattern.split('*') {
        if part.is_empty() {
            continue;
        }
        if let Some(idx) = remainder.find(part) {
            if is_first && idx != 0 {
                return false;
            }
            remainder = &remainder[idx + part.len()..];
        } else {
            return false;
        }
        is_first = false;
    }

    if !pattern.ends_with('*') {
        if let Some(last) = pattern.split('*').last() {
            return remainder.is_empty() && (last.is_empty() || pattern.ends_with(last));
        }
    }
    true
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Not,
    And,
    Or,
    LParen,
    RParen,
    Selector(String, String),
}

pub fn parse_predicate(input: &str) -> Result<AopPredicate, String> {
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
            _ => {
                let mut name = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_alphanumeric() || ch == '_' {
                        name.push(ch);
                        chars.next();
                    } else {
                        break;
                    }
                }
                if name.is_empty() {
                    return Err(format!("unexpected character '{}'", c));
                }
                while let Some(&ch) = chars.peek() {
                    if ch.is_whitespace() {
                        chars.next();
                    } else {
                        break;
                    }
                }
                if chars.peek() != Some(&'(') {
                    return Err(format!("expected '(' after selector '{}'", name));
                }
                chars.next();
                let mut arg = String::new();
                let mut depth = 1usize;
                while let Some(ch) = chars.next() {
                    match ch {
                        '(' => {
                            depth += 1;
                            arg.push(ch);
                        }
                        ')' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                            arg.push(ch);
                        }
                        _ => arg.push(ch),
                    }
                }
                if depth != 0 {
                    return Err("unclosed selector argument".to_string());
                }
                tokens.push(Token::Selector(name, arg.trim().to_string()));
            }
        }
    }
    Ok(tokens)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, pos: 0 }
    }

    fn parse_expr(&mut self) -> Result<AopPredicate, String> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<AopPredicate, String> {
        let mut expr = self.parse_and()?;
        while matches!(self.peek_token(), Some(Token::Or)) {
            self.pos += 1;
            let rhs = self.parse_and()?;
            expr = AopPredicate::Or(Box::new(expr), Box::new(rhs));
        }
        Ok(expr)
    }

    fn parse_and(&mut self) -> Result<AopPredicate, String> {
        let mut expr = self.parse_not()?;
        while matches!(self.peek_token(), Some(Token::And)) {
            self.pos += 1;
            let rhs = self.parse_not()?;
            expr = AopPredicate::And(Box::new(expr), Box::new(rhs));
        }
        Ok(expr)
    }

    fn parse_not(&mut self) -> Result<AopPredicate, String> {
        if matches!(self.peek_token(), Some(Token::Not)) {
            self.pos += 1;
            let inner = self.parse_not()?;
            return Ok(AopPredicate::Not(Box::new(inner)));
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<AopPredicate, String> {
        if matches!(self.peek_token(), Some(Token::LParen)) {
            self.pos += 1;
            let expr = self.parse_expr()?;
            if !matches!(self.peek_token(), Some(Token::RParen)) {
                return Err("expected ')'".to_string());
            }
            self.pos += 1;
            return Ok(expr);
        }
        if let Some(Token::Selector(name, arg)) = self.peek_token().cloned() {
            self.pos += 1;
            let selector = match name.as_str() {
                "init" => AopSelector::Init(arg),
                "within" => AopSelector::Within(arg),
                "attr" => AopSelector::Attr(arg),
                _ => return Err(format!("illegal selector '{}' for runtime AOP", name)),
            };
            return Ok(AopPredicate::Selector(selector));
        }
        Err("expected selector or '('".to_string())
    }

    fn peek_token(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }
}

pub fn parse_aop_config(toml: &toml::Value) -> Result<Option<AopConfig>, String> {
    let Some(aspects_table) = toml.get("aspects").and_then(|v| v.as_table()) else {
        return Ok(None);
    };
    let Some(runtime_table) = aspects_table.get("runtime").and_then(|v| v.as_table()) else {
        return Ok(None);
    };

    let runtime_enabled = runtime_table
        .get("enabled")
        .and_then(|v| v.as_bool())
        .unwrap_or(true);

    let around_values = match runtime_table.get("around") {
        None => Vec::new(),
        Some(value) => value
            .as_array()
            .ok_or_else(|| "aspects.runtime.around must be an array".to_string())?
            .clone(),
    };

    let mut around = Vec::new();
    for (idx, rule_val) in around_values.iter().enumerate() {
        let rule = rule_val.as_table().ok_or_else(|| {
            format!("aspects.runtime.around[{}] must be a table", idx)
        })?;

        let predicate_raw = rule
            .get("on")
            .or_else(|| rule.get("predicate"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| {
                format!("aspects.runtime.around[{}] missing 'on' predicate", idx)
            })?;
        let advice = rule
            .get("use")
            .or_else(|| rule.get("advice"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| {
                format!("aspects.runtime.around[{}] missing 'use' advice", idx)
            })?;

        let priority = rule
            .get("priority")
            .and_then(|v| v.as_integer())
            .unwrap_or(0);

        let predicate = parse_predicate(predicate_raw)?;
        around.push(AopAroundRule {
            predicate,
            advice: advice.to_string(),
            priority,
            order: idx,
            raw_predicate: predicate_raw.to_string(),
        });
    }

    Ok(Some(AopConfig {
        runtime_enabled,
        around,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_runtime_aop_config() {
        let toml: toml::Value = r#"
[aspects.runtime]
enabled = true
around = [
  { on = "pc{ init(Foo) }", use = "around_fn", priority = 10 }
]
"#
        .parse()
        .expect("parse toml");
        let config = parse_aop_config(&toml).expect("parse aop");
        let config = config.expect("config present");
        assert!(config.runtime_enabled);
        assert_eq!(config.around.len(), 1);
        let ctx = AopMatchContext {
            type_name: "Foo",
            module_path: "Foo",
            attrs: &[],
        };
        assert!(config.around[0].predicate.matches(&ctx));
    }
}
