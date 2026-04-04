#[cfg(test)]
mod tests {
    use crate::lexer::Lexer;
    use crate::token::{FStringToken, TokenKind};

    fn find_errors(source: &str) -> Vec<(usize, usize, String)> {
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize();
        let mut errors = Vec::new();
        for tok in &tokens {
            if let TokenKind::Error(msg) = &tok.kind {
                errors.push((tok.span.line, tok.span.column, msg.clone()));
            }
        }
        errors
    }

    fn get_fstring_tokens(source: &str) -> Vec<TokenKind> {
        let mut lexer = Lexer::new(source);
        let tokens = lexer.tokenize();
        tokens
            .into_iter()
            .filter_map(|tok| match tok.kind {
                TokenKind::FString(_) => Some(tok.kind),
                TokenKind::Error(_) => Some(tok.kind),
                _ => None,
            })
            .collect()
    }

    // ===== File-level regression tests =====

    // NOTE: ffi_usage.spl and profile.spl use multi-line double-quoted strings
    // which the self-hosted Simple parser supports but are not safe to enable in
    // the Rust parser (causes 16+ regressions in other files). Skipped.

    #[test]
    fn test_utilities_file() {
        let source = include_str!("../../../lib/common/serialization/utilities.spl");
        let errors = find_errors(source);
        for (line, col, msg) in &errors {
            eprintln!("utilities.spl: line {} col {}: {}", line, col, msg);
        }
        assert!(errors.is_empty(), "Expected no errors, got: {:?}", errors);
    }

    // ===== Targeted pattern tests =====

    /// Literal brace in string without closing } (the utilities.spl pattern)
    /// "{v: " should parse the { as a literal character since the expression
    /// scanning hits the closing " before finding a matching }
    #[test]
    fn test_literal_brace_in_string() {
        let source = r#"val x = "{v: ""#;
        let errors = find_errors(source);
        assert!(
            errors.is_empty(),
            "Literal brace in string should not error: {:?}",
            errors
        );
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], FStringToken::Literal("{v: ".to_string()));
            }
            other => panic!("Expected FString with literal, got: {:?}", other),
        }
    }

    /// The exact pattern from utilities.spl line 153:
    /// "{v: {version}, data: " + serialized + "}"
    #[test]
    fn test_utilities_version_pattern() {
        let source = r#"val x = "{v: {version}, data: " + serialized + "}""#;
        let errors = find_errors(source);
        assert!(errors.is_empty(), "Version pattern should not error: {:?}", errors);
    }

    /// String starting with { that contains a valid interpolation later
    #[test]
    fn test_brace_before_valid_interpolation() {
        let source = r#"val x = "{key}: {value}""#;
        let errors = find_errors(source);
        assert!(
            errors.is_empty(),
            "Brace before interpolation should not error: {:?}",
            errors
        );
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                // {key} should be treated as interpolation, not literal
                // because the expression scanner finds } before "
                assert!(parts.iter().any(|p| *p == FStringToken::Expr("key".to_string())));
                assert!(parts.iter().any(|p| *p == FStringToken::Expr("value".to_string())));
            }
            other => panic!("Expected FString, got: {:?}", other),
        }
    }

    /// The starts_with pattern from utilities.spl line 157
    #[test]
    fn test_starts_with_brace_string() {
        let source = r#"if not x.starts_with("{v: "):"#;
        let errors = find_errors(source);
        assert!(
            errors.is_empty(),
            "starts_with brace string should not error: {:?}",
            errors
        );
    }

    /// Normal interpolation still works
    #[test]
    fn test_normal_interpolation_still_works() {
        let source = r#"val x = "hello {name}!""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 3);
                assert_eq!(parts[0], FStringToken::Literal("hello ".to_string()));
                assert_eq!(parts[1], FStringToken::Expr("name".to_string()));
                assert_eq!(parts[2], FStringToken::Literal("!".to_string()));
            }
            other => panic!("Expected FString, got: {:?}", other),
        }
    }

    /// {{ escape still works
    #[test]
    fn test_double_brace_escape_still_works() {
        let source = r#"val x = "literal {{braces}}""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], FStringToken::Literal("literal {braces}".to_string()));
            }
            other => panic!("Expected FString with literal braces, got: {:?}", other),
        }
    }

    // =========================================================================
    // Format specifier tests
    // =========================================================================

    #[test]
    fn test_format_spec_float_precision() {
        // {pi:.2f} should parse as ExprWithFormat("pi", ".2f")
        let source = r#"val x = "{pi:.2f}""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], FStringToken::ExprWithFormat("pi".to_string(), ".2f".to_string()));
            }
            other => panic!("Expected FString with format spec, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_spec_zero_padded_int() {
        // {count:05d} should parse as ExprWithFormat("count", "05d")
        let source = r#"val x = "{count:05d}""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], FStringToken::ExprWithFormat("count".to_string(), "05d".to_string()));
            }
            other => panic!("Expected FString with format spec, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_spec_right_align() {
        // {name:>20} should parse as ExprWithFormat("name", ">20")
        let source = r#"val x = "{name:>20}""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], FStringToken::ExprWithFormat("name".to_string(), ">20".to_string()));
            }
            other => panic!("Expected FString with format spec, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_spec_percentage() {
        // {ratio:.1%} should parse as ExprWithFormat("ratio", ".1%")
        let source = r#"val x = "{ratio:.1%}""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], FStringToken::ExprWithFormat("ratio".to_string(), ".1%".to_string()));
            }
            other => panic!("Expected FString with format spec, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_spec_with_literal_parts() {
        // "value: {x:.3f} end" should have Literal, ExprWithFormat, Literal
        let source = r#"val x = "value: {x:.3f} end""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 3);
                assert_eq!(parts[0], FStringToken::Literal("value: ".to_string()));
                assert_eq!(parts[1], FStringToken::ExprWithFormat("x".to_string(), ".3f".to_string()));
                assert_eq!(parts[2], FStringToken::Literal(" end".to_string()));
            }
            other => panic!("Expected FString with format spec and literals, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_spec_hex() {
        // {val:x} should parse as ExprWithFormat("val", "x")
        let source = r#"val x = "{val:x}""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], FStringToken::ExprWithFormat("val".to_string(), "x".to_string()));
            }
            other => panic!("Expected FString with hex format spec, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_spec_center_align_with_fill() {
        // {text:*^20} should parse as ExprWithFormat("text", "*^20")
        let source = r#"val x = "{text:*^20}""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 1);
                assert_eq!(parts[0], FStringToken::ExprWithFormat("text".to_string(), "*^20".to_string()));
            }
            other => panic!("Expected FString with center-aligned format spec, got: {:?}", other),
        }
    }

    #[test]
    fn test_format_spec_does_not_interfere_with_plain_interpolation() {
        // {name} without format spec should still work
        let source = r#"val x = "Hello {name}!""#;
        let tokens = get_fstring_tokens(source);
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenKind::FString(parts) => {
                assert_eq!(parts.len(), 3);
                assert_eq!(parts[0], FStringToken::Literal("Hello ".to_string()));
                assert_eq!(parts[1], FStringToken::Expr("name".to_string()));
                assert_eq!(parts[2], FStringToken::Literal("!".to_string()));
            }
            other => panic!("Expected plain FString, got: {:?}", other),
        }
    }
}
