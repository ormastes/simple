//! Unified truthiness rules for Simple language.
//!
//! Truthiness determines how values are coerced to boolean in conditionals.
//! This is the single source of truth - both interpreter and codegen MUST
//! use these rules.

/// Truthiness evaluation rules.
///
/// # Language Semantics
///
/// In Simple, the following values are considered falsy:
/// - `false`
/// - `0` (integer)
/// - `0.0` (float)
/// - `""` (empty string)
/// - `[]` (empty array)
/// - `()` (empty tuple)
/// - `{}` (empty dict)
/// - `nil`
///
/// All other values are truthy, including:
/// - Non-zero numbers
/// - Non-empty strings
/// - Non-empty collections
/// - Objects, functions, lambdas, actors, etc.
pub struct TruthinessRules;

impl TruthinessRules {
    /// Evaluate truthiness of a value.
    ///
    /// # Arguments
    ///
    /// * `from_bool` - If the value is a boolean
    /// * `from_int` - If the value is an integer
    /// * `from_float` - If the value is a float
    /// * `is_empty_collection` - If the value is a collection, whether it's empty
    /// * `is_nil` - If the value is nil
    ///
    /// # Returns
    ///
    /// `true` if the value is truthy, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// // Bool truthiness
    /// TruthinessRules::is_truthy(Some(true), None, None, None, false)  // true
    /// TruthinessRules::is_truthy(Some(false), None, None, None, false) // false
    ///
    /// // Int truthiness
    /// TruthinessRules::is_truthy(None, Some(1), None, None, false)   // true
    /// TruthinessRules::is_truthy(None, Some(0), None, None, false)   // false
    /// TruthinessRules::is_truthy(None, Some(-1), None, None, false)  // true
    ///
    /// // Float truthiness
    /// TruthinessRules::is_truthy(None, None, Some(0.1), None, false)  // true
    /// TruthinessRules::is_truthy(None, None, Some(0.0), None, false)  // false
    ///
    /// // Collection truthiness
    /// TruthinessRules::is_truthy(None, None, None, Some(true), false)  // false (empty)
    /// TruthinessRules::is_truthy(None, None, None, Some(false), false) // true (non-empty)
    ///
    /// // Nil truthiness
    /// TruthinessRules::is_truthy(None, None, None, None, true)  // false
    /// ```
    pub fn is_truthy(
        from_bool: Option<bool>,
        from_int: Option<i64>,
        from_float: Option<f64>,
        is_empty_collection: Option<bool>,
        is_nil: bool,
    ) -> bool {
        // Nil is always falsy
        if is_nil {
            return false;
        }

        // Bool: direct value
        if let Some(b) = from_bool {
            return b;
        }

        // Int: non-zero is truthy
        if let Some(i) = from_int {
            return i != 0;
        }

        // Float: non-zero is truthy
        if let Some(f) = from_float {
            return f != 0.0;
        }

        // Collection: empty is falsy
        if let Some(is_empty) = is_empty_collection {
            return !is_empty;
        }

        // All other values (objects, functions, etc.) are truthy
        true
    }

    /// Check if a specific type is always truthy.
    ///
    /// Some types are always truthy regardless of their value:
    /// - Functions
    /// - Lambdas
    /// - Closures
    /// - Objects
    /// - Actors
    /// - Channels
    /// - etc.
    pub fn is_always_truthy_type(type_name: &str) -> bool {
        matches!(
            type_name,
            "Function"
                | "Lambda"
                | "Closure"
                | "Object"
                | "Actor"
                | "Channel"
                | "Future"
                | "Generator"
                | "ThreadPool"
                | "Mock"
                | "Matcher"
                | "NativeFunction"
                | "EnumType"
                | "EnumVariant"
                | "Constructor"
                | "TraitObject"
                | "Block"
        )
    }

    /// Check if a type's truthiness depends on its value.
    pub fn is_value_dependent_type(type_name: &str) -> bool {
        matches!(
            type_name,
            "Bool" | "Int" | "Float" | "String" | "Array" | "Tuple" | "Dict" | "Nil"
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bool_truthiness() {
        assert!(TruthinessRules::is_truthy(Some(true), None, None, None, false));
        assert!(!TruthinessRules::is_truthy(Some(false), None, None, None, false));
    }

    #[test]
    fn test_int_truthiness() {
        assert!(TruthinessRules::is_truthy(None, Some(1), None, None, false));
        assert!(TruthinessRules::is_truthy(None, Some(-1), None, None, false));
        assert!(TruthinessRules::is_truthy(None, Some(42), None, None, false));
        assert!(!TruthinessRules::is_truthy(None, Some(0), None, None, false));
    }

    #[test]
    fn test_float_truthiness() {
        assert!(TruthinessRules::is_truthy(None, None, Some(0.1), None, false));
        assert!(TruthinessRules::is_truthy(None, None, Some(-0.1), None, false));
        assert!(!TruthinessRules::is_truthy(None, None, Some(0.0), None, false));
    }

    #[test]
    fn test_collection_truthiness() {
        // Empty collections are falsy
        assert!(!TruthinessRules::is_truthy(None, None, None, Some(true), false));
        // Non-empty collections are truthy
        assert!(TruthinessRules::is_truthy(None, None, None, Some(false), false));
    }

    #[test]
    fn test_nil_truthiness() {
        assert!(!TruthinessRules::is_truthy(None, None, None, None, true));
    }

    #[test]
    fn test_default_truthy() {
        // Unknown values (no specific type) are truthy by default
        assert!(TruthinessRules::is_truthy(None, None, None, None, false));
    }

    #[test]
    fn test_always_truthy_types() {
        assert!(TruthinessRules::is_always_truthy_type("Function"));
        assert!(TruthinessRules::is_always_truthy_type("Lambda"));
        assert!(TruthinessRules::is_always_truthy_type("Object"));
        assert!(!TruthinessRules::is_always_truthy_type("Int"));
        assert!(!TruthinessRules::is_always_truthy_type("Bool"));
    }
}
