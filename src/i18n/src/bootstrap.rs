/// Bootstrap messages used when catalogs can't be loaded
///
/// These are minimal English error messages hardcoded in Rust to handle
/// the bootstrap problem: if we can't parse Simple files (due to parser errors),
/// we still need error messages to report those errors.
///
/// These are only used as a last resort fallback.
use crate::message::InterpolatedMessage;

/// Minimal set of bootstrap error messages
pub const BOOTSTRAP_MESSAGES: &[(&str, &str, &str)] = &[
    // (error_code, title, message)
    ("E0001", "Syntax Error", "Syntax error"),
    ("E0002", "Unexpected Token", "Unexpected token"),
    ("E0003", "Unexpected End of File", "Unexpected end of file"),
    ("E0004", "Invalid Integer Literal", "Invalid integer literal"),
    ("E0005", "Invalid Float Literal", "Invalid float literal"),
    ("E0006", "Invalid Escape Sequence", "Invalid escape sequence"),
    ("E0007", "Unclosed String Literal", "Unclosed string literal"),
    ("E0008", "Invalid Indentation", "Invalid indentation"),
    ("E0009", "Unterminated Block Comment", "Unterminated block comment"),
    ("E0010", "Missing Expected Token", "Missing expected token"),
    ("E0011", "Invalid Pattern", "Invalid pattern"),
    ("E0012", "Invalid Type", "Invalid type"),
];

/// Get a bootstrap message by error code
pub fn get_bootstrap_message(id: &str) -> Option<InterpolatedMessage> {
    BOOTSTRAP_MESSAGES
        .iter()
        .find(|(code, _, _)| *code == id)
        .map(|(code, title, message)| InterpolatedMessage {
            id: code.to_string(),
            title: title.to_string(),
            message: message.to_string(),
            label: None,
            help: None,
            note: None,
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bootstrap_messages() {
        let msg = get_bootstrap_message("E0002").unwrap();
        assert_eq!(msg.id, "E0002");
        assert_eq!(msg.title, "Unexpected Token");
        assert!(msg.message.contains("Unexpected token"));
    }

    #[test]
    fn test_bootstrap_message_not_found() {
        let msg = get_bootstrap_message("E9999");
        assert!(msg.is_none());
    }
}
