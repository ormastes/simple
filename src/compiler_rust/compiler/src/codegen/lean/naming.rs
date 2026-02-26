//! Lean naming conventions for Simple to Lean translation.
//!
//! This module provides consistent identifier transformation functions
//! for translating Simple names to Lean naming conventions:
//! - PascalCase for types, classes, structures, and theorems
//! - camelCase for functions, methods, and variables

/// Convert a snake_case Simple name to PascalCase for Lean types/theorems.
///
/// # Examples
/// ```
/// use simple_compiler::codegen::lean::naming::to_pascal_case;
///
/// assert_eq!(to_pascal_case("my_type"), "MyType");
/// assert_eq!(to_pascal_case("simple"), "Simple");
/// assert_eq!(to_pascal_case("ref_capability"), "RefCapability");
/// ```
pub fn to_pascal_case(name: &str) -> String {
    name.split('_')
        .map(|s| {
            let mut chars = s.chars();
            match chars.next() {
                None => String::new(),
                Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
            }
        })
        .collect()
}

/// Convert a snake_case Simple name to camelCase for Lean functions/variables.
///
/// # Examples
/// ```
/// use simple_compiler::codegen::lean::naming::to_camel_case;
///
/// assert_eq!(to_camel_case("my_function"), "myFunction");
/// assert_eq!(to_camel_case("get_value"), "getValue");
/// assert_eq!(to_camel_case("simple"), "simple");
/// ```
pub fn to_camel_case(name: &str) -> String {
    let mut result = String::new();
    let mut capitalize_next = false;

    for (i, c) in name.chars().enumerate() {
        if c == '_' {
            capitalize_next = true;
        } else if capitalize_next {
            result.push(c.to_ascii_uppercase());
            capitalize_next = false;
        } else if i == 0 {
            result.push(c.to_ascii_lowercase());
        } else {
            result.push(c);
        }
    }

    result
}

/// Sanitize an identifier for Lean by escaping reserved words.
///
/// Lean has some reserved keywords that need escaping with «» brackets.
pub fn sanitize_lean_ident(name: &str) -> String {
    const LEAN_RESERVED: &[&str] = &[
        "let",
        "in",
        "if",
        "then",
        "else",
        "do",
        "return",
        "match",
        "with",
        "def",
        "theorem",
        "lemma",
        "example",
        "structure",
        "class",
        "instance",
        "where",
        "fun",
        "forall",
        "exists",
        "namespace",
        "section",
        "variable",
        "open",
        "import",
        "inductive",
        "mutual",
        "end",
        "private",
        "protected",
        "Type",
        "Prop",
        "Sort",
        "by",
        "have",
        "show",
        "from",
        "at",
        "as",
    ];

    if LEAN_RESERVED.contains(&name) {
        format!("«{}»", name)
    } else {
        name.to_string()
    }
}

/// Convert to PascalCase and sanitize for Lean identifiers.
pub fn to_lean_type_name(name: &str) -> String {
    sanitize_lean_ident(&to_pascal_case(name))
}

/// Convert to camelCase and sanitize for Lean identifiers.
pub fn to_lean_func_name(name: &str) -> String {
    sanitize_lean_ident(&to_camel_case(name))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_pascal_case() {
        assert_eq!(to_pascal_case("my_type"), "MyType");
        assert_eq!(to_pascal_case("simple"), "Simple");
        assert_eq!(to_pascal_case("ref_capability"), "RefCapability");
        assert_eq!(to_pascal_case("a_b_c"), "ABC");
        assert_eq!(to_pascal_case(""), "");
    }

    #[test]
    fn test_to_camel_case() {
        assert_eq!(to_camel_case("my_function"), "myFunction");
        assert_eq!(to_camel_case("get_value"), "getValue");
        assert_eq!(to_camel_case("simple"), "simple");
        assert_eq!(to_camel_case("UPPER"), "uPPER");
        assert_eq!(to_camel_case(""), "");
    }

    #[test]
    fn test_sanitize_reserved() {
        assert_eq!(sanitize_lean_ident("let"), "«let»");
        assert_eq!(sanitize_lean_ident("def"), "«def»");
        assert_eq!(sanitize_lean_ident("myVar"), "myVar");
        assert_eq!(sanitize_lean_ident("Type"), "«Type»");
    }

    #[test]
    fn test_combined_functions() {
        assert_eq!(to_lean_type_name("my_type"), "MyType");
        assert_eq!(to_lean_func_name("my_function"), "myFunction");
        // Reserved word after conversion
        assert_eq!(to_lean_type_name("type"), "«Type»");
    }
}
