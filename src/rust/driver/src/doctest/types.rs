use std::path::PathBuf;

/// Expected outcome for a doctest example.
#[derive(Debug, Clone, PartialEq)]
pub enum Expected {
    Output(String),
    Error(String),
    Empty,
}

/// A single doctest example parsed from a source file.
#[derive(Debug, Clone, PartialEq)]
pub struct DoctestExample {
    pub source: PathBuf,
    pub start_line: usize,
    pub commands: Vec<String>,
    pub expected: Expected,
    /// Section name extracted from nearest markdown heading + sequential number
    /// Example: "Stack Operations #1", "Stack Operations #2"
    pub section_name: Option<String>,
}

/// Result of running a doctest example.
#[derive(Debug, Clone, PartialEq)]
pub struct DoctestResult {
    pub example: DoctestExample,
    pub status: DoctestStatus,
    pub actual: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DoctestStatus {
    Passed,
    Failed(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expected_variants() {
        let empty = Expected::Empty;
        let output = Expected::Output("test".to_string());
        let error = Expected::Error("error".to_string());

        assert!(matches!(empty, Expected::Empty));
        assert!(matches!(output, Expected::Output(_)));
        assert!(matches!(error, Expected::Error(_)));
    }

    #[test]
    fn test_doctest_status() {
        let passed = DoctestStatus::Passed;
        let failed = DoctestStatus::Failed("reason".to_string());

        assert!(matches!(passed, DoctestStatus::Passed));
        assert!(matches!(failed, DoctestStatus::Failed(_)));
    }
}
