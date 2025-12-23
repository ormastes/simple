//! Dependency injection configuration and predicate parsing.

use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiMode {
    Hybrid,
    Manual,
}

impl DiMode {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "hybrid" => Ok(DiMode::Hybrid),
            "manual" => Ok(DiMode::Manual),
            _ => Err(format!("unknown di.mode '{}'", value)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiScope {
    Singleton,
    Transient,
}

impl DiScope {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "Singleton" | "singleton" => Ok(DiScope::Singleton),
            "Transient" | "transient" => Ok(DiScope::Transient),
            _ => Err(format!("unknown scope '{}'", value)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiSelector {
    Type(String),
    Within(String),
    Attr(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiPredicate {
    Selector(DiSelector),
    Not(Box<DiPredicate>),
    And(Box<DiPredicate>, Box<DiPredicate>),
    Or(Box<DiPredicate>, Box<DiPredicate>),
}

#[derive(Debug, Clone)]
pub struct DiBindingRule {
    pub predicate: DiPredicate,
    pub impl_type: String,
    pub scope: DiScope,
    pub priority: i64,
    pub order: usize,
    pub raw_predicate: String,
}

#[derive(Debug, Clone, Default)]
pub struct DiProfile {
    pub bindings: Vec<DiBindingRule>,
}

#[derive(Debug, Clone)]
pub struct DiConfig {
    pub mode: DiMode,
    pub profiles: HashMap<String, DiProfile>,
}

#[derive(Debug, Clone)]
pub struct DiMatchContext<'a> {
    pub type_name: &'a str,
    pub module_path: &'a str,
    pub attrs: &'a [String],
}

#[derive(Debug, Clone)]
pub struct DiResolveError {
    pub profile: String,
    pub matches: Vec<(String, i64, i32)>,
}

impl DiConfig {
    pub fn select_binding(
        &self,
        profile: &str,
        ctx: &DiMatchContext<'_>,
    ) -> Result<Option<&DiBindingRule>, DiResolveError> {
        let Some(profile_cfg) = self.profiles.get(profile) else {
            return Ok(None);
        };

        let mut matches = Vec::new();
        for binding in &profile_cfg.bindings {
            if binding.predicate.matches(ctx) {
                let specificity = binding.predicate.specificity();
                matches.push((binding, specificity));
            }
        }

        if matches.is_empty() {
            return Ok(None);
        }

        matches.sort_by(|(a, a_spec), (b, b_spec)| {
            a.priority
                .cmp(&b.priority)
                .then_with(|| a_spec.cmp(b_spec))
                .then_with(|| b.order.cmp(&a.order))
        });

        let (winner, _) = matches.last().unwrap();
        Ok(Some(*winner))
    }
}

impl DiPredicate {
    pub fn matches(&self, ctx: &DiMatchContext<'_>) -> bool {
        match self {
            DiPredicate::Selector(sel) => match sel {
                DiSelector::Type(pattern) => match_pattern(pattern, ctx.type_name),
                DiSelector::Within(pattern) => match_pattern(pattern, ctx.module_path),
                DiSelector::Attr(name) => ctx.attrs.iter().any(|a| a == name),
            },
            DiPredicate::Not(inner) => !inner.matches(ctx),
            DiPredicate::And(lhs, rhs) => lhs.matches(ctx) && rhs.matches(ctx),
            DiPredicate::Or(lhs, rhs) => lhs.matches(ctx) || rhs.matches(ctx),
        }
    }

    pub fn specificity(&self) -> i32 {
        match self {
            DiPredicate::Selector(sel) => selector_specificity(sel),
            DiPredicate::Not(inner) => inner.specificity() - 1,
            DiPredicate::And(lhs, rhs) => lhs.specificity() + rhs.specificity(),
            DiPredicate::Or(lhs, rhs) => lhs.specificity().max(rhs.specificity()),
        }
    }
}

fn selector_specificity(sel: &DiSelector) -> i32 {
    match sel {
        DiSelector::Attr(_) => 2,
        DiSelector::Type(pattern) | DiSelector::Within(pattern) => {
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
    let mut parts = pattern.split('*').peekable();
    let mut remainder = value;
    let mut is_first = true;

    while let Some(part) = parts.next() {
        if part.is_empty() {
            is_first = false;
            continue;
        }
        if is_first {
            if !remainder.starts_with(part) {
                return false;
            }
            remainder = &remainder[part.len()..];
        } else if let Some(idx) = remainder.find(part) {
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

pub fn parse_predicate(input: &str) -> Result<DiPredicate, String> {
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
            _ if c.is_ascii_alphabetic() || c == '_' => {
                let mut name = String::new();
                while let Some(&ch) = chars.peek() {
                    if ch.is_ascii_alphanumeric() || ch == '_' {
                        name.push(ch);
                        chars.next();
                    } else {
                        break;
                    }
                }
                while let Some(&ch) = chars.peek() {
                    if ch.is_ascii_whitespace() {
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
                while let Some(ch) = chars.next() {
                    if ch == ')' {
                        break;
                    }
                    arg.push(ch);
                }
                if arg.is_empty() {
                    return Err(format!("selector '{}' missing argument", name));
                }
                tokens.push(Token::Selector(name, arg.trim().to_string()));
            }
            _ => {
                return Err(format!("unexpected character '{}' in predicate", c));
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

    fn parse_expr(&mut self) -> Result<DiPredicate, String> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<DiPredicate, String> {
        let mut node = self.parse_and()?;
        while self.match_token(Token::Or) {
            let rhs = self.parse_and()?;
            node = DiPredicate::Or(Box::new(node), Box::new(rhs));
        }
        Ok(node)
    }

    fn parse_and(&mut self) -> Result<DiPredicate, String> {
        let mut node = self.parse_not()?;
        while self.match_token(Token::And) {
            let rhs = self.parse_not()?;
            node = DiPredicate::And(Box::new(node), Box::new(rhs));
        }
        Ok(node)
    }

    fn parse_not(&mut self) -> Result<DiPredicate, String> {
        if self.match_token(Token::Not) {
            let inner = self.parse_not()?;
            Ok(DiPredicate::Not(Box::new(inner)))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Result<DiPredicate, String> {
        if self.match_token(Token::LParen) {
            let expr = self.parse_expr()?;
            if !self.match_token(Token::RParen) {
                return Err("expected ')'".to_string());
            }
            return Ok(expr);
        }

        if let Some(Token::Selector(name, arg)) = self.peek_token() {
            let name = name.clone();
            let arg = arg.clone();
            self.pos += 1;
            let selector = match name.as_str() {
                "type" => DiSelector::Type(arg),
                "within" => DiSelector::Within(arg),
                "attr" => DiSelector::Attr(arg),
                _ => return Err(format!("illegal selector '{}' for DI", name)),
            };
            return Ok(DiPredicate::Selector(selector));
        }

        Err("expected selector or '('".to_string())
    }

    fn match_token(&mut self, expected: Token) -> bool {
        if let Some(tok) = self.tokens.get(self.pos) {
            if *tok == expected {
                self.pos += 1;
                return true;
            }
        }
        false
    }

    fn peek_token(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }
}

pub fn parse_di_config(toml: &toml::Value) -> Result<Option<DiConfig>, String> {
    let Some(di_table) = toml.get("di").and_then(|v| v.as_table()) else {
        return Ok(None);
    };

    let mode = di_table
        .get("mode")
        .and_then(|v| v.as_str())
        .map(DiMode::parse)
        .transpose()?
        .unwrap_or(DiMode::Hybrid);

    let mut profiles = HashMap::new();
    if let Some(profiles_table) = di_table.get("profiles").and_then(|v| v.as_table()) {
        for (profile_name, profile_value) in profiles_table {
            let mut profile = DiProfile::default();
            let bindings = match profile_value.get("bindings") {
                None => Vec::new(),
                Some(value) => value
                    .as_array()
                    .ok_or_else(|| {
                        format!("di.profiles.{}.bindings must be an array", profile_name)
                    })?
                    .clone(),
            };

            for (idx, binding_val) in bindings.iter().enumerate() {
                let binding = binding_val.as_table().ok_or_else(|| {
                    format!(
                        "di.profiles.{}.bindings[{}] must be a table",
                        profile_name, idx
                    )
                })?;

                let predicate_raw = binding
                    .get("on")
                    .or_else(|| binding.get("predicate"))
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| {
                        format!(
                            "di.profiles.{}.bindings[{}] missing 'on' predicate",
                            profile_name, idx
                        )
                    })?;
                let predicate = parse_predicate(predicate_raw)?;

                let impl_type = binding
                    .get("impl")
                    .or_else(|| binding.get("impl_type"))
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| {
                        format!(
                            "di.profiles.{}.bindings[{}] missing 'impl' type",
                            profile_name, idx
                        )
                    })?
                    .to_string();

                let scope = binding
                    .get("scope")
                    .and_then(|v| v.as_str())
                    .map(DiScope::parse)
                    .transpose()?
                    .unwrap_or(DiScope::Transient);

                let priority = binding
                    .get("priority")
                    .and_then(|v| v.as_integer())
                    .unwrap_or(0);

                profile.bindings.push(DiBindingRule {
                    predicate,
                    impl_type,
                    scope,
                    priority,
                    order: idx,
                    raw_predicate: predicate_raw.to_string(),
                });
            }

            profiles.insert(profile_name.clone(), profile);
        }
    }

    Ok(Some(DiConfig { mode, profiles }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_predicate_basic() {
        let pred = parse_predicate("pc{ type(Foo) & !attr(test) }").unwrap();
        let ctx = DiMatchContext {
            type_name: "Foo",
            module_path: "app.core",
            attrs: &["release".into()],
        };
        assert!(pred.matches(&ctx));
    }

    #[test]
    fn parse_di_config_basic() {
        let toml: toml::Value = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
  { on = "pc{ type(Foo) }", impl = "Bar", scope = "Singleton", priority = 10 }
]
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        assert_eq!(config.mode, DiMode::Hybrid);
        let profile = config.profiles.get("default").unwrap();
        assert_eq!(profile.bindings.len(), 1);
        assert_eq!(profile.bindings[0].impl_type, "Bar");
        assert_eq!(profile.bindings[0].priority, 10);
        assert_eq!(profile.bindings[0].scope, DiScope::Singleton);
    }

    #[test]
    fn match_pattern_segments() {
        assert!(match_pattern("app.**", "app.core.user"));
        assert!(match_pattern("app.*.user", "app.core.user"));
        assert!(!match_pattern("app.*.user", "app.core.auth.user"));
        assert!(match_pattern("app.service*", "app.service_v2"));
    }
}
