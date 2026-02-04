//! Error Code Explanations for LLM Tools
//!
//! Provides detailed explanations for compiler error codes in machine-readable format.
//! This enables LLM tools to understand errors and provide better assistance.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Detailed explanation for an error code
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorExplanation {
    /// Error code (e.g., "E1001")
    pub code: String,
    /// Short title
    pub title: String,
    /// Detailed description
    pub description: String,
    /// Common causes
    pub causes: Vec<String>,
    /// How to fix it
    pub fixes: Vec<String>,
    /// Example code that triggers the error
    pub example_bad: Option<String>,
    /// Example fix for the error
    pub example_good: Option<String>,
    /// Related error codes
    pub related: Vec<String>,
}

impl ErrorExplanation {
    pub fn new(code: impl Into<String>, title: impl Into<String>) -> Self {
        Self {
            code: code.into(),
            title: title.into(),
            description: String::new(),
            causes: Vec::new(),
            fixes: Vec::new(),
            example_bad: None,
            example_good: None,
            related: Vec::new(),
        }
    }

    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = desc.into();
        self
    }

    pub fn with_cause(mut self, cause: impl Into<String>) -> Self {
        self.causes.push(cause.into());
        self
    }

    pub fn with_fix(mut self, fix: impl Into<String>) -> Self {
        self.fixes.push(fix.into());
        self
    }

    pub fn with_example_bad(mut self, example: impl Into<String>) -> Self {
        self.example_bad = Some(example.into());
        self
    }

    pub fn with_example_good(mut self, example: impl Into<String>) -> Self {
        self.example_good = Some(example.into());
        self
    }

    pub fn with_related(mut self, code: impl Into<String>) -> Self {
        self.related.push(code.into());
        self
    }
}

/// Registry of error explanations
pub struct ErrorRegistry {
    explanations: HashMap<String, ErrorExplanation>,
}

impl ErrorRegistry {
    pub fn new() -> Self {
        let mut registry = Self {
            explanations: HashMap::new(),
        };
        registry.register_all();
        registry
    }

    fn register(&mut self, explanation: ErrorExplanation) {
        self.explanations.insert(explanation.code.clone(), explanation);
    }

    pub fn get(&self, code: &str) -> Option<&ErrorExplanation> {
        self.explanations.get(code)
    }

    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(&self.explanations)
    }

    pub fn to_json_compact(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(&self.explanations)
    }

    fn register_all(&mut self) {
        // E1001: Undefined Variable
        self.register(
            ErrorExplanation::new("E1001", "Undefined Variable")
                .with_description("Attempted to use a variable that hasn't been declared")
                .with_cause("Variable name was misspelled")
                .with_cause("Variable was used before declaration")
                .with_cause("Variable is out of scope")
                .with_fix("Check the spelling of the variable name")
                .with_fix("Declare the variable before using it")
                .with_fix("Ensure the variable is in scope")
                .with_example_bad("fn main():\n    print(count)  # Error: count not defined")
                .with_example_good("fn main():\n    let count = 0\n    print(count)  # OK")
                .with_related("E1002"),
        );

        // E1002: Undefined Function
        self.register(
            ErrorExplanation::new("E1002", "Undefined Function")
                .with_description("Attempted to call a function that doesn't exist")
                .with_cause("Function name was misspelled")
                .with_cause("Function not imported")
                .with_cause("Function defined after use")
                .with_fix("Check the spelling of the function name")
                .with_fix("Import the function from the correct module")
                .with_fix("Define the function before calling it")
                .with_example_bad("fn main():\n    result = calcualte(42)  # Typo!")
                .with_example_good("fn main():\n    result = calculate(42)  # Correct")
                .with_related("E1001")
                .with_related("E1010"),
        );

        // E1003: Type Mismatch
        self.register(
            ErrorExplanation::new("E1003", "Type Mismatch")
                .with_description("Expression has incompatible type")
                .with_cause("Wrong type provided to function")
                .with_cause("Cannot convert between types")
                .with_cause("Return type doesn't match declaration")
                .with_fix("Convert the value to the expected type")
                .with_fix("Change the function signature")
                .with_fix("Use type casting if appropriate")
                .with_example_bad("fn add(x: i64, y: i64) -> i64:\n    return x + y\n\nadd(\"5\", 10)  # Error!")
                .with_example_good("fn add(x: i64, y: i64) -> i64:\n    return x + y\n\nadd(5, 10)  # OK")
                .with_related("E1004"),
        );

        // E1101: Break Outside Loop
        self.register(
            ErrorExplanation::new("E1101", "Break Outside Loop")
                .with_description("Break statement can only be used inside loops")
                .with_cause("Break used in non-loop context")
                .with_cause("Misplaced break statement")
                .with_fix("Move break inside a loop")
                .with_fix("Remove the break statement")
                .with_example_bad("fn main():\n    if true:\n        break  # Error!")
                .with_example_good("fn main():\n    for i in 0..10:\n        if i > 5:\n            break  # OK")
                .with_related("E1102"),
        );

        // E1102: Continue Outside Loop
        self.register(
            ErrorExplanation::new("E1102", "Continue Outside Loop")
                .with_description("Continue statement can only be used inside loops")
                .with_cause("Continue used in non-loop context")
                .with_fix("Move continue inside a loop")
                .with_fix("Remove the continue statement")
                .with_related("E1101"),
        );

        // E3001: Division by Zero
        self.register(
            ErrorExplanation::new("E3001", "Division by Zero")
                .with_description("Attempted to divide by zero at runtime")
                .with_cause("Divisor is zero")
                .with_cause("Variable evaluated to zero")
                .with_fix("Check if divisor is zero before dividing")
                .with_fix("Use checked_div() for safe division")
                .with_example_bad("let x = 10 / 0  # Runtime error!")
                .with_example_good("let divisor = 0\nif divisor != 0:\n    let x = 10 / divisor")
                .with_related("E3002"),
        );

        // E3002: Index Out of Bounds
        self.register(
            ErrorExplanation::new("E3002", "Index Out of Bounds")
                .with_description("Attempted to access array index that doesn't exist")
                .with_cause("Index is negative")
                .with_cause("Index >= array length")
                .with_fix("Check array bounds before accessing")
                .with_fix("Use .get() method for safe access")
                .with_example_bad("let arr = [1, 2, 3]\nlet x = arr[10]  # Error!")
                .with_example_good("let arr = [1, 2, 3]\nif 10 < arr.len():\n    let x = arr[10]")
                .with_related("E3001"),
        );
    }
}

impl Default for ErrorRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_explanation_builder() {
        let explanation = ErrorExplanation::new("E1001", "Test Error")
            .with_description("Test description")
            .with_cause("Cause 1")
            .with_cause("Cause 2")
            .with_fix("Fix 1")
            .with_example_bad("bad code")
            .with_example_good("good code")
            .with_related("E1002");

        assert_eq!(explanation.code, "E1001");
        assert_eq!(explanation.title, "Test Error");
        assert_eq!(explanation.causes.len(), 2);
        assert_eq!(explanation.fixes.len(), 1);
        assert!(explanation.example_bad.is_some());
        assert_eq!(explanation.related.len(), 1);
    }

    #[test]
    fn test_error_registry() {
        let registry = ErrorRegistry::new();

        // Check some common errors are registered
        assert!(registry.get("E1001").is_some());
        assert!(registry.get("E1002").is_some());
        assert!(registry.get("E1003").is_some());
        assert!(registry.get("E1101").is_some());
        assert!(registry.get("E3001").is_some());

        // Check details
        let e1001 = registry.get("E1001").unwrap();
        assert_eq!(e1001.title, "Undefined Variable");
        assert!(!e1001.causes.is_empty());
        assert!(!e1001.fixes.is_empty());
        assert!(e1001.example_bad.is_some());
        assert!(e1001.example_good.is_some());
    }

    #[test]
    fn test_json_serialization() {
        let registry = ErrorRegistry::new();
        let json = registry.to_json().unwrap();

        // Verify it's valid JSON
        let value: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert!(value.is_object());
        assert!(value.get("E1001").is_some());

        // Verify structure
        let e1001 = &value["E1001"];
        assert_eq!(e1001["code"], "E1001");
        assert_eq!(e1001["title"], "Undefined Variable");
        assert!(e1001["causes"].is_array());
        assert!(e1001["fixes"].is_array());
    }

    #[test]
    fn test_json_compact() {
        let registry = ErrorRegistry::new();
        let compact = registry.to_json_compact().unwrap();
        let pretty = registry.to_json().unwrap();

        // Compact should be shorter
        assert!(compact.len() < pretty.len());

        // Both should parse to same structure
        let compact_val: serde_json::Value = serde_json::from_str(&compact).unwrap();
        let pretty_val: serde_json::Value = serde_json::from_str(&pretty).unwrap();
        assert_eq!(compact_val, pretty_val);
    }
}
