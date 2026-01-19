use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// A localized message with all its components
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct LocalizedMessage {
    /// Message ID (e.g., "E0002")
    pub id: String,

    /// Short title for the error
    pub title: String,

    /// Main message template with {placeholders}
    pub message: String,

    /// Optional label template for code spans
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,

    /// Optional help text template
    #[serde(skip_serializing_if = "Option::is_none")]
    pub help: Option<String>,

    /// Optional note template
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
}

/// Context for message interpolation
#[derive(Debug, Default, Clone)]
pub struct MessageContext {
    values: HashMap<String, String>,
}

impl MessageContext {
    /// Create a new empty context
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a key-value pair for interpolation
    pub fn insert(&mut self, key: impl Into<String>, value: impl Into<String>) -> &mut Self {
        self.values.insert(key.into(), value.into());
        self
    }

    /// Get a value by key
    pub fn get(&self, key: &str) -> Option<&str> {
        self.values.get(key).map(|s| s.as_str())
    }

    /// Interpolate a template string with context values
    ///
    /// Replaces {key} placeholders with values from the context.
    /// If a key is not found, the placeholder is left unchanged.
    pub fn interpolate(&self, template: &str) -> String {
        let mut result = template.to_string();

        for (key, value) in &self.values {
            let placeholder = format!("{{{}}}", key);
            result = result.replace(&placeholder, value);
        }

        result
    }
}

impl LocalizedMessage {
    /// Interpolate all fields of the message with the given context
    pub fn interpolate(&self, ctx: &MessageContext) -> InterpolatedMessage {
        InterpolatedMessage {
            id: self.id.clone(),
            title: ctx.interpolate(&self.title),
            message: ctx.interpolate(&self.message),
            label: self.label.as_ref().map(|l| ctx.interpolate(l)),
            help: self.help.as_ref().map(|h| ctx.interpolate(h)),
            note: self.note.as_ref().map(|n| ctx.interpolate(n)),
        }
    }
}

/// A message with all placeholders interpolated
#[derive(Debug, Clone, PartialEq)]
pub struct InterpolatedMessage {
    pub id: String,
    pub title: String,
    pub message: String,
    pub label: Option<String>,
    pub help: Option<String>,
    pub note: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_interpolate() {
        let mut ctx = MessageContext::new();
        ctx.insert("expected", "identifier");
        ctx.insert("found", "number");

        let template = "expected {expected}, found {found}";
        let result = ctx.interpolate(template);

        assert_eq!(result, "expected identifier, found number");
    }

    #[test]
    fn test_context_interpolate_missing_key() {
        let ctx = MessageContext::new();
        let template = "expected {expected}";
        let result = ctx.interpolate(template);

        // Missing keys are left unchanged
        assert_eq!(result, "expected {expected}");
    }

    #[test]
    fn test_message_interpolate() {
        let message = LocalizedMessage {
            id: "E0002".to_string(),
            title: "Unexpected Token".to_string(),
            message: "expected {expected}, found {found}".to_string(),
            label: Some("expected {expected} here".to_string()),
            help: Some("try adding `{expected}`".to_string()),
            note: None,
        };

        let mut ctx = MessageContext::new();
        ctx.insert("expected", "identifier");
        ctx.insert("found", "number");

        let interpolated = message.interpolate(&ctx);

        assert_eq!(interpolated.id, "E0002");
        assert_eq!(interpolated.title, "Unexpected Token");
        assert_eq!(interpolated.message, "expected identifier, found number");
        assert_eq!(interpolated.label, Some("expected identifier here".to_string()));
        assert_eq!(interpolated.help, Some("try adding `identifier`".to_string()));
        assert_eq!(interpolated.note, None);
    }

    #[test]
    fn test_korean_interpolation() {
        let message = LocalizedMessage {
            id: "E0002".to_string(),
            title: "예상치 못한 토큰".to_string(),
            message: "{expected}을(를) 예상했지만 {found}을(를) 발견했습니다".to_string(),
            label: Some("여기에 {expected}이(가) 필요합니다".to_string()),
            help: None,
            note: None,
        };

        let mut ctx = MessageContext::new();
        ctx.insert("expected", "식별자");
        ctx.insert("found", "숫자");

        let interpolated = message.interpolate(&ctx);

        assert_eq!(interpolated.message, "식별자을(를) 예상했지만 숫자을(를) 발견했습니다");
        assert_eq!(interpolated.label, Some("여기에 식별자이(가) 필요합니다".to_string()));
    }
}
