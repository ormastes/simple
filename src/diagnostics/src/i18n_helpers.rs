//! I18n helper functions for diagnostics

use simple_i18n::MessageContext;

/// Helper trait for types that can be inserted into a message context
pub trait IntoContextValue {
    fn into_context_value(self) -> String;
}

impl IntoContextValue for String {
    fn into_context_value(self) -> String {
        self
    }
}

impl IntoContextValue for &str {
    fn into_context_value(self) -> String {
        self.to_string()
    }
}

impl IntoContextValue for i32 {
    fn into_context_value(self) -> String {
        self.to_string()
    }
}

impl IntoContextValue for i64 {
    fn into_context_value(self) -> String {
        self.to_string()
    }
}

impl IntoContextValue for usize {
    fn into_context_value(self) -> String {
        self.to_string()
    }
}

impl IntoContextValue for bool {
    fn into_context_value(self) -> String {
        self.to_string()
    }
}

/// Create a message context with a single key-value pair
///
/// # Examples
///
/// ```
/// use simple_diagnostics::i18n::ctx1;
///
/// let ctx = ctx1("expected", "identifier");
/// ```
pub fn ctx1(key: &str, value: impl IntoContextValue) -> MessageContext {
    let mut ctx = MessageContext::new();
    ctx.insert(key, &value.into_context_value());
    ctx
}

/// Create a message context with two key-value pairs
///
/// # Examples
///
/// ```
/// use simple_diagnostics::i18n::ctx2;
///
/// let ctx = ctx2("expected", "i32", "found", "bool");
/// ```
pub fn ctx2(
    key1: &str,
    value1: impl IntoContextValue,
    key2: &str,
    value2: impl IntoContextValue,
) -> MessageContext {
    let mut ctx = MessageContext::new();
    ctx.insert(key1, &value1.into_context_value());
    ctx.insert(key2, &value2.into_context_value());
    ctx
}

/// Create a message context with three key-value pairs
///
/// # Examples
///
/// ```
/// use simple_diagnostics::i18n::ctx3;
///
/// let ctx = ctx3("expected", "i32", "found", "bool", "line", 42);
/// ```
pub fn ctx3(
    key1: &str,
    value1: impl IntoContextValue,
    key2: &str,
    value2: impl IntoContextValue,
    key3: &str,
    value3: impl IntoContextValue,
) -> MessageContext {
    let mut ctx = MessageContext::new();
    ctx.insert(key1, &value1.into_context_value());
    ctx.insert(key2, &value2.into_context_value());
    ctx.insert(key3, &value3.into_context_value());
    ctx
}

/// Builder for creating message contexts fluently
///
/// # Examples
///
/// ```
/// use simple_diagnostics::i18n::ContextBuilder;
///
/// let ctx = ContextBuilder::new()
///     .with("expected", "identifier")
///     .with("found", "number")
///     .with("line", 42)
///     .build();
/// ```
pub struct ContextBuilder {
    ctx: MessageContext,
}

impl ContextBuilder {
    pub fn new() -> Self {
        Self {
            ctx: MessageContext::new(),
        }
    }

    pub fn with(mut self, key: &str, value: impl IntoContextValue) -> Self {
        self.ctx.insert(key, &value.into_context_value());
        self
    }

    pub fn build(self) -> MessageContext {
        self.ctx
    }
}

impl Default for ContextBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ctx1() {
        let ctx = ctx1("name", "Alice");
        assert_eq!(ctx.get("name"), Some("Alice"));
    }

    #[test]
    fn test_ctx2() {
        let ctx = ctx2("expected", "i32", "found", "bool");
        assert_eq!(ctx.get("expected"), Some("i32"));
        assert_eq!(ctx.get("found"), Some("bool"));
    }

    #[test]
    fn test_ctx3() {
        let ctx = ctx3("a", "1", "b", "2", "c", "3");
        assert_eq!(ctx.get("a"), Some("1"));
        assert_eq!(ctx.get("b"), Some("2"));
        assert_eq!(ctx.get("c"), Some("3"));
    }

    #[test]
    fn test_context_builder() {
        let ctx = ContextBuilder::new()
            .with("expected", "identifier")
            .with("found", "number")
            .with("line", 42)
            .build();

        assert_eq!(ctx.get("expected"), Some("identifier"));
        assert_eq!(ctx.get("found"), Some("number"));
        assert_eq!(ctx.get("line"), Some("42"));
    }

    #[test]
    fn test_into_context_value_types() {
        let ctx = ContextBuilder::new()
            .with("string", "hello")
            .with("int", 42)
            .with("bool", true)
            .with("usize", 100_usize)
            .build();

        assert_eq!(ctx.get("string"), Some("hello"));
        assert_eq!(ctx.get("int"), Some("42"));
        assert_eq!(ctx.get("bool"), Some("true"));
        assert_eq!(ctx.get("usize"), Some("100"));
    }
}
