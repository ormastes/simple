# string_methods_spec

*Source: `simple/std_lib/test/features/stdlib/string_methods_spec.spl`*

---

Enhanced text Methods - Feature #203

Overview:
    Comprehensive string methods including substring, find, replace, trim,
    case conversion, split, and more. Over 30 string methods for complete
    text manipulation. All methods implemented in Rust interpreter.

Syntax:
    text.substring(0, 5)
    text.find("pattern")
    text.contains("sub")
    text.starts_with("pre")
    text.trim()
    text.to_upper()
    text.split(",")
    text.lines()

Implementation:
    - Substring operations: substring, char_at, chars
    - Search operations: find, contains, starts_with, ends_with
    - Whitespace operations: trim, trim_start, trim_end
    - Case operations: to_upper, to_lower
    - Split and join: split, lines
    - Replacement: replace
    - Additional: repeat, reverse, is_empty, len, count

Notes:
    - All methods implemented in Rust interpreter
    - Supports both aliased method names (trim/strip, find/index_of)
    - Comprehensive coverage for text manipulation
