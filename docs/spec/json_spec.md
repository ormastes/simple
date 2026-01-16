# json_spec

*Source: `simple/std_lib/test/features/stdlib/json_spec.spl`*

---

JSON Library - Feature #200

Overview:
    Full JSON library with parsing, serialization, and builder API. Supports
    JsonValue enum (Null, bool, Number, Integer, text, Array, Object),
    recursive descent parser, and pretty-printing. Pure Simple implementation
    used by MCP protocol for structured data.

Syntax:
    val result = json.parse(json_string)
    val json_str = json.stringify(value)
    val builder = JsonBuilder.new()
        .set_string("name", "bob")
        .set_int("age", 25)
        .to_string()

Implementation:
    - JsonValue enum for all JSON types
    - Recursive descent parser for JSON strings
    - Serialization with compact and pretty modes
    - JsonBuilder fluent API for construction
    - Supports nested objects and arrays
    - Handles all JSON primitives correctly

Notes:
    - Pure Simple implementation
    - Used by MCP protocol for structured data
    - Pretty-printing with configurable indentation
