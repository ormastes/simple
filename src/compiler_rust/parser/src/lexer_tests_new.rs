use super::*;
use pretty_assertions::assert_eq;

fn tokenize(source: &str) -> Vec<TokenKind> {
    let mut lexer = Lexer::new(source);
    lexer.tokenize().into_iter().map(|t| t.kind).collect()
}

// Split into 4 files for better organization:
// - lexer_tests_literals.rs: Literal and keyword tokenization
// - lexer_tests_syntax.rs: Operators, delimiters, expressions, indentation
// - lexer_tests_comments.rs: Comment tokenization
// - lexer_tests_features.rs: Module system, functions, string units, AOP

include!("lexer_tests_literals.rs");
include!("lexer_tests_syntax.rs");
include!("lexer_tests_comments.rs");
include!("lexer_tests_features.rs");
