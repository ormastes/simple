//! Built-in method definitions.
//!
//! This module defines all built-in methods for primitive and collection types.
//! These definitions serve as the single source of truth for both interpreter
//! and codegen dispatch.

use super::registry::{MethodInfo, RuntimeFn};

/// Array built-in methods.
pub static ARRAY_METHODS: &[MethodInfo] = &[
    MethodInfo {
        name: "len",
        runtime_fn: RuntimeFn::Simple("rt_array_len"),
        param_count: 0,
        is_mutating: false,
        description: "returns the number of elements",
    },
    MethodInfo {
        name: "push",
        runtime_fn: RuntimeFn::Simple("rt_array_push"),
        param_count: 1,
        is_mutating: true,
        description: "appends an element to the end",
    },
    MethodInfo {
        name: "pop",
        runtime_fn: RuntimeFn::Simple("rt_array_pop"),
        param_count: 0,
        is_mutating: true,
        description: "removes and returns the last element",
    },
    MethodInfo {
        name: "get",
        runtime_fn: RuntimeFn::Simple("rt_index_get"),
        param_count: 1,
        is_mutating: false,
        description: "returns element at index",
    },
    MethodInfo {
        name: "set",
        runtime_fn: RuntimeFn::Simple("rt_index_set"),
        param_count: 2,
        is_mutating: true,
        description: "sets element at index",
    },
    MethodInfo {
        name: "clear",
        runtime_fn: RuntimeFn::Simple("rt_array_clear"),
        param_count: 0,
        is_mutating: true,
        description: "removes all elements",
    },
    MethodInfo {
        name: "contains",
        runtime_fn: RuntimeFn::Simple("rt_contains"),
        param_count: 1,
        is_mutating: false,
        description: "checks if element exists",
    },
    MethodInfo {
        name: "slice",
        runtime_fn: RuntimeFn::Simple("rt_slice"),
        param_count: 2,
        is_mutating: false,
        description: "returns a subarray",
    },
    MethodInfo {
        name: "first",
        runtime_fn: RuntimeFn::Simple("rt_array_first"),
        param_count: 0,
        is_mutating: false,
        description: "returns the first element",
    },
    MethodInfo {
        name: "last",
        runtime_fn: RuntimeFn::Simple("rt_array_last"),
        param_count: 0,
        is_mutating: false,
        description: "returns the last element",
    },
    MethodInfo {
        name: "is_empty",
        runtime_fn: RuntimeFn::Simple("rt_array_is_empty"),
        param_count: 0,
        is_mutating: false,
        description: "checks if array has no elements",
    },
    MethodInfo {
        name: "reverse",
        runtime_fn: RuntimeFn::Simple("rt_array_reverse"),
        param_count: 0,
        is_mutating: true,
        description: "reverses elements in place",
    },
    MethodInfo {
        name: "sort",
        runtime_fn: RuntimeFn::Simple("rt_array_sort"),
        param_count: 0,
        is_mutating: true,
        description: "sorts elements in place",
    },
    MethodInfo {
        name: "clone",
        runtime_fn: RuntimeFn::Simple("rt_array_clone"),
        param_count: 0,
        is_mutating: false,
        description: "creates a shallow copy",
    },
    MethodInfo {
        name: "extend",
        runtime_fn: RuntimeFn::Simple("rt_array_extend"),
        param_count: 1,
        is_mutating: true,
        description: "appends all elements from another array",
    },
    MethodInfo {
        name: "insert",
        runtime_fn: RuntimeFn::Simple("rt_array_insert"),
        param_count: 2,
        is_mutating: true,
        description: "inserts element at index",
    },
    MethodInfo {
        name: "remove",
        runtime_fn: RuntimeFn::Simple("rt_array_remove"),
        param_count: 1,
        is_mutating: true,
        description: "removes element at index",
    },
];

/// Dict built-in methods.
pub static DICT_METHODS: &[MethodInfo] = &[
    MethodInfo {
        name: "len",
        runtime_fn: RuntimeFn::Simple("rt_dict_len"),
        param_count: 0,
        is_mutating: false,
        description: "returns the number of key-value pairs",
    },
    MethodInfo {
        name: "get",
        runtime_fn: RuntimeFn::Simple("rt_index_get"),
        param_count: 1,
        is_mutating: false,
        description: "returns value for key",
    },
    MethodInfo {
        name: "set",
        runtime_fn: RuntimeFn::Simple("rt_dict_set"),
        param_count: 2,
        is_mutating: true,
        description: "sets value for key",
    },
    MethodInfo {
        name: "clear",
        runtime_fn: RuntimeFn::Simple("rt_dict_clear"),
        param_count: 0,
        is_mutating: true,
        description: "removes all key-value pairs",
    },
    MethodInfo {
        name: "keys",
        runtime_fn: RuntimeFn::Simple("rt_dict_keys"),
        param_count: 0,
        is_mutating: false,
        description: "returns array of keys",
    },
    MethodInfo {
        name: "values",
        runtime_fn: RuntimeFn::Simple("rt_dict_values"),
        param_count: 0,
        is_mutating: false,
        description: "returns array of values",
    },
    MethodInfo {
        name: "contains",
        runtime_fn: RuntimeFn::Simple("rt_contains"),
        param_count: 1,
        is_mutating: false,
        description: "checks if key exists",
    },
    MethodInfo {
        name: "remove",
        runtime_fn: RuntimeFn::Simple("rt_dict_remove"),
        param_count: 1,
        is_mutating: true,
        description: "removes key-value pair",
    },
    MethodInfo {
        name: "is_empty",
        runtime_fn: RuntimeFn::Simple("rt_dict_is_empty"),
        param_count: 0,
        is_mutating: false,
        description: "checks if dict has no pairs",
    },
    MethodInfo {
        name: "clone",
        runtime_fn: RuntimeFn::Simple("rt_dict_clone"),
        param_count: 0,
        is_mutating: false,
        description: "creates a shallow copy",
    },
    MethodInfo {
        name: "merge",
        runtime_fn: RuntimeFn::Simple("rt_dict_merge"),
        param_count: 1,
        is_mutating: false,
        description: "merges another dict",
    },
    MethodInfo {
        name: "items",
        runtime_fn: RuntimeFn::Simple("rt_dict_items"),
        param_count: 0,
        is_mutating: false,
        description: "returns (key, value) tuples",
    },
    MethodInfo {
        name: "get_or",
        runtime_fn: RuntimeFn::Simple("rt_dict_get_or"),
        param_count: 2,
        is_mutating: false,
        description: "returns value or default",
    },
];

/// String built-in methods.
pub static STRING_METHODS: &[MethodInfo] = &[
    MethodInfo {
        name: "len",
        runtime_fn: RuntimeFn::Simple("rt_string_len"),
        param_count: 0,
        is_mutating: false,
        description: "returns the string length in bytes",
    },
    MethodInfo {
        name: "concat",
        runtime_fn: RuntimeFn::Simple("rt_string_concat"),
        param_count: 1,
        is_mutating: false,
        description: "concatenates with another string",
    },
    MethodInfo {
        name: "contains",
        runtime_fn: RuntimeFn::Simple("rt_contains"),
        param_count: 1,
        is_mutating: false,
        description: "checks if substring exists",
    },
    MethodInfo {
        name: "slice",
        runtime_fn: RuntimeFn::Simple("rt_slice"),
        param_count: 2,
        is_mutating: false,
        description: "returns a substring",
    },
    MethodInfo {
        name: "starts_with",
        runtime_fn: RuntimeFn::Simple("rt_string_starts_with"),
        param_count: 1,
        is_mutating: false,
        description: "checks if string starts with prefix",
    },
    MethodInfo {
        name: "ends_with",
        runtime_fn: RuntimeFn::Simple("rt_string_ends_with"),
        param_count: 1,
        is_mutating: false,
        description: "checks if string ends with suffix",
    },
    MethodInfo {
        name: "trim",
        runtime_fn: RuntimeFn::Simple("rt_string_trim"),
        param_count: 0,
        is_mutating: false,
        description: "removes leading/trailing whitespace",
    },
    MethodInfo {
        name: "to_upper",
        runtime_fn: RuntimeFn::Simple("rt_string_to_upper"),
        param_count: 0,
        is_mutating: false,
        description: "converts to uppercase",
    },
    MethodInfo {
        name: "to_lower",
        runtime_fn: RuntimeFn::Simple("rt_string_to_lower"),
        param_count: 0,
        is_mutating: false,
        description: "converts to lowercase",
    },
    MethodInfo {
        name: "split",
        runtime_fn: RuntimeFn::Simple("rt_string_split"),
        param_count: 1,
        is_mutating: false,
        description: "splits by delimiter",
    },
    MethodInfo {
        name: "replace",
        runtime_fn: RuntimeFn::Simple("rt_string_replace"),
        param_count: 2,
        is_mutating: false,
        description: "replaces occurrences of pattern",
    },
    MethodInfo {
        name: "chars",
        runtime_fn: RuntimeFn::Simple("rt_string_chars"),
        param_count: 0,
        is_mutating: false,
        description: "returns array of characters",
    },
    MethodInfo {
        name: "is_empty",
        runtime_fn: RuntimeFn::Simple("rt_string_is_empty"),
        param_count: 0,
        is_mutating: false,
        description: "checks if string is empty",
    },
];

/// Tuple built-in methods.
pub static TUPLE_METHODS: &[MethodInfo] = &[
    MethodInfo {
        name: "len",
        runtime_fn: RuntimeFn::Simple("rt_tuple_len"),
        param_count: 0,
        is_mutating: false,
        description: "returns the number of elements",
    },
    MethodInfo {
        name: "get",
        runtime_fn: RuntimeFn::Simple("rt_index_get"),
        param_count: 1,
        is_mutating: false,
        description: "returns element at index",
    },
    MethodInfo {
        name: "set",
        runtime_fn: RuntimeFn::Simple("rt_tuple_set"),
        param_count: 2,
        is_mutating: true,
        description: "sets element at index",
    },
];

/// Option built-in methods.
pub static OPTION_METHODS: &[MethodInfo] = &[
    MethodInfo {
        name: "is_some",
        runtime_fn: RuntimeFn::Simple("rt_option_is_some"),
        param_count: 0,
        is_mutating: false,
        description: "checks if option contains a value",
    },
    MethodInfo {
        name: "is_none",
        runtime_fn: RuntimeFn::Simple("rt_option_is_none"),
        param_count: 0,
        is_mutating: false,
        description: "checks if option is empty",
    },
    MethodInfo {
        name: "unwrap",
        runtime_fn: RuntimeFn::Simple("rt_option_unwrap"),
        param_count: 0,
        is_mutating: false,
        description: "returns value, panics if none",
    },
    MethodInfo {
        name: "unwrap_or",
        runtime_fn: RuntimeFn::Simple("rt_option_unwrap_or"),
        param_count: 1,
        is_mutating: false,
        description: "returns value or default",
    },
    MethodInfo {
        name: "expect",
        runtime_fn: RuntimeFn::Simple("rt_option_expect"),
        param_count: 1,
        is_mutating: false,
        description: "returns value, panics with message if none",
    },
    MethodInfo {
        name: "map",
        runtime_fn: RuntimeFn::Simple("rt_option_map"),
        param_count: 1,
        is_mutating: false,
        description: "transforms value if present",
    },
    MethodInfo {
        name: "and_then",
        runtime_fn: RuntimeFn::Simple("rt_option_and_then"),
        param_count: 1,
        is_mutating: false,
        description: "chains option-returning function",
    },
];

/// Int built-in methods.
pub static INT_METHODS: &[MethodInfo] = &[
    MethodInfo {
        name: "abs",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns absolute value",
    },
    MethodInfo {
        name: "to_string",
        runtime_fn: RuntimeFn::Simple("rt_int_to_string"),
        param_count: 0,
        is_mutating: false,
        description: "converts to string",
    },
    MethodInfo {
        name: "to_float",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "converts to float",
    },
    MethodInfo {
        name: "clamp",
        runtime_fn: RuntimeFn::Inline,
        param_count: 2,
        is_mutating: false,
        description: "clamps to range [min, max]",
    },
    MethodInfo {
        name: "pow",
        runtime_fn: RuntimeFn::Simple("rt_int_pow"),
        param_count: 1,
        is_mutating: false,
        description: "raises to power",
    },
];

/// Float built-in methods.
pub static FLOAT_METHODS: &[MethodInfo] = &[
    MethodInfo {
        name: "abs",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns absolute value",
    },
    MethodInfo {
        name: "floor",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "rounds down to integer",
    },
    MethodInfo {
        name: "ceil",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "rounds up to integer",
    },
    MethodInfo {
        name: "round",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "rounds to nearest integer",
    },
    MethodInfo {
        name: "to_string",
        runtime_fn: RuntimeFn::Simple("rt_float_to_string"),
        param_count: 0,
        is_mutating: false,
        description: "converts to string",
    },
    MethodInfo {
        name: "to_int",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "truncates to integer",
    },
    MethodInfo {
        name: "is_nan",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "checks if NaN",
    },
    MethodInfo {
        name: "is_infinite",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "checks if infinite",
    },
    MethodInfo {
        name: "sqrt",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns square root",
    },
    MethodInfo {
        name: "pow",
        runtime_fn: RuntimeFn::Simple("rt_float_pow"),
        param_count: 1,
        is_mutating: false,
        description: "raises to power",
    },
    MethodInfo {
        name: "sin",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns sine",
    },
    MethodInfo {
        name: "cos",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns cosine",
    },
    MethodInfo {
        name: "tan",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns tangent",
    },
    MethodInfo {
        name: "exp",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns e^x",
    },
    MethodInfo {
        name: "ln",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns natural logarithm",
    },
    MethodInfo {
        name: "log10",
        runtime_fn: RuntimeFn::Inline,
        param_count: 0,
        is_mutating: false,
        description: "returns base-10 logarithm",
    },
];

/// All built-in methods for convenient iteration.
pub static BUILTIN_METHODS: &[(&str, &[MethodInfo])] = &[
    ("Array", ARRAY_METHODS),
    ("Dict", DICT_METHODS),
    ("String", STRING_METHODS),
    ("Tuple", TUPLE_METHODS),
    ("Option", OPTION_METHODS),
    ("Int", INT_METHODS),
    ("Float", FLOAT_METHODS),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_methods_complete() {
        let names: Vec<_> = ARRAY_METHODS.iter().map(|m| m.name).collect();
        assert!(names.contains(&"len"));
        assert!(names.contains(&"push"));
        assert!(names.contains(&"pop"));
        assert!(names.contains(&"get"));
        assert!(names.contains(&"set"));
        assert!(names.contains(&"clear"));
        assert!(names.contains(&"contains"));
        assert!(names.contains(&"slice"));
    }

    #[test]
    fn test_dict_methods_complete() {
        let names: Vec<_> = DICT_METHODS.iter().map(|m| m.name).collect();
        assert!(names.contains(&"len"));
        assert!(names.contains(&"get"));
        assert!(names.contains(&"set"));
        assert!(names.contains(&"clear"));
        assert!(names.contains(&"keys"));
        assert!(names.contains(&"values"));
    }

    #[test]
    fn test_runtime_fn_names() {
        for info in ARRAY_METHODS {
            if let RuntimeFn::Simple(name) = info.runtime_fn {
                assert!(name.starts_with("rt_"), "Runtime fn should start with rt_: {}", name);
            }
        }
    }

    #[test]
    fn test_mutating_methods_flagged() {
        // These should be mutating
        let mutating: Vec<_> = ARRAY_METHODS.iter().filter(|m| m.is_mutating).map(|m| m.name).collect();
        assert!(mutating.contains(&"push"));
        assert!(mutating.contains(&"pop"));
        assert!(mutating.contains(&"clear"));
        assert!(mutating.contains(&"set"));

        // These should NOT be mutating
        let non_mutating: Vec<_> = ARRAY_METHODS
            .iter()
            .filter(|m| !m.is_mutating)
            .map(|m| m.name)
            .collect();
        assert!(non_mutating.contains(&"len"));
        assert!(non_mutating.contains(&"get"));
        assert!(non_mutating.contains(&"contains"));
    }
}
