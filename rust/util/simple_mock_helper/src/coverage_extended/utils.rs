//! Utility functions for coverage analysis

use rustc_demangle::demangle;

/// Demangle a Rust symbol name to human-readable form.
/// Cleans up the output to remove crate hashes and angle brackets.
pub fn demangle_rust_name(mangled: &str) -> String {
    let demangled = demangle(mangled).to_string();

    // Clean up the demangled name:
    // 1. Remove crate hashes like [8088a71b75a8e98d]
    // 2. Remove leading < and trailing > from impl blocks
    // 3. Remove generic parameters like ::<T>

    let mut cleaned = demangled.clone();

    // Remove crate hashes [hex]
    while let Some(start) = cleaned.find('[') {
        if let Some(end) = cleaned[start..].find(']') {
            let hash = &cleaned[start + 1..start + end];
            if hash.chars().all(|c| c.is_ascii_hexdigit()) {
                cleaned = format!("{}{}", &cleaned[..start], &cleaned[start + end + 1..]);
                continue;
            }
        }
        break;
    }

    // Remove leading < from impl blocks like <Type>::method
    if cleaned.starts_with('<') {
        if let Some(end) = cleaned.find(">::") {
            cleaned = format!("{}{}", &cleaned[1..end], &cleaned[end + 1..]);
        }
    }

    // Remove hash suffix like ::h1234abcd
    if let Some(idx) = cleaned.rfind("::h") {
        if cleaned[idx + 3..].chars().all(|c| c.is_ascii_hexdigit()) {
            cleaned = cleaned[..idx].to_string();
        }
    }

    // Remove generic parameters ::<...> at the end
    while let Some(idx) = cleaned.rfind("::<") {
        if cleaned[idx..].rfind('>').is_some() {
            cleaned = cleaned[..idx].to_string();
        } else {
            break;
        }
    }

    cleaned
}

/// Check if a demangled function name matches a type::method pattern
/// Handles various naming conventions and module paths
pub fn matches_type_method(demangled: &str, type_name: &str, method_name: &str) -> bool {
    // Extract just the type part from the spec (e.g., "simple_driver::Runner" -> "Runner")
    let spec_type = type_name.split("::").last().unwrap_or(type_name);

    // Check if the demangled name ends with Type::method
    let suffix = format!("{}::{}", spec_type, method_name);
    if demangled.ends_with(&suffix) {
        return true;
    }

    // Also check full path match
    let full_match = format!("{}::{}", type_name, method_name);
    if demangled.contains(&full_match) {
        return true;
    }

    false
}
