use thiserror::Error;

/// Parse error type
#[derive(Debug, Clone, Error)]
pub enum ParseError {
    #[error(
        "Unexpected token: expected {expected}, found {found} at line {line}, column {column}"
    )]
    UnexpectedToken {
        expected: String,
        found: String,
        line: usize,
        column: usize,
    },
    #[error("Unexpected end of file")]
    UnexpectedEof,
    #[error("Invalid template: {message} at line {line}, column {column}")]
    InvalidTemplate {
        message: String,
        line: usize,
        column: usize,
    },
    #[error("Unclosed block: {block_type} at line {line}, column {column}")]
    UnclosedBlock {
        block_type: String,
        line: usize,
        column: usize,
    },
}
