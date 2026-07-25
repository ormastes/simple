# JSON Serialization Implementation - 2026-01-20

## Summary

Implemented comprehensive JSON serialization library for the Simple stdlib, removing 2 TODOs from the codebase. The implementation provides a pure Simple JSON builder with support for objects, arrays, and all JSON primitives.

## Implementation Overview

**Module:** `simple/std_lib/src/data/json.spl` (300 lines)

**Types:**
- `JsonValue` - Enum representing any JSON value
- `JsonObject` - Builder for JSON objects
- `JsonArray` - Builder for JSON arrays

**Features:**
- Pure Simple implementation (no FFI required)
- Pretty-printing and compact output
- Proper string escaping
- Type-safe builder API
- Chainable method calls

## JSON API

### JsonValue Enum

```simple
pub enum JsonValue:
    Object(List<(text, JsonValue)>)
    Array(List<JsonValue>)
    String(text)
    Number(f64)
    Bool(bool)
    Null
```

**Methods:**
```simple
pub fn to_string() -> text                              # Compact JSON
pub fn to_pretty_string() -> text                       # Pretty-printed JSON
```

### JsonObject Builder

```simple
pub struct JsonObject:
    pairs: List<(text, JsonValue)>
```

**Methods:**
```simple
# Constructor
pub static fn new() -> JsonObject

# Add fields
pub me add_string(key: text, value: text)
pub me add_number(key: text, value: f64)
pub me add_bool(key: text, value: bool)
pub me add_null(key: text)
pub me add_array(key: text, value: JsonArray)
pub me add_object(key: text, value: JsonObject)
pub me add_value(key: text, value: JsonValue)

# Convert and serialize
pub fn to_value() -> JsonValue
pub fn to_string() -> text
pub fn to_pretty_string() -> text
```

### JsonArray Builder

```simple
pub struct JsonArray:
    items: List<JsonValue>
```

**Methods:**
```simple
# Constructor
pub static fn new() -> JsonArray

# Add elements
pub me push_string(value: text)
pub me push_number(value: f64)
pub me push_bool(value: bool)
pub me push_null()
pub me push_array(value: JsonArray)
pub me push_object(value: JsonObject)
pub me push_value(value: JsonValue)

# Convert and serialize
pub fn to_value() -> JsonValue
pub fn to_string() -> text
pub fn to_pretty_string() -> text
```

### Convenience Functions

```simple
pub fn json_object() -> JsonObject
pub fn json_array() -> JsonArray
pub fn to_json(value: JsonValue) -> text
pub fn to_json_pretty(value: JsonValue) -> text
```

## Usage Examples

### Basic Object Creation

```simple
use data.json.{json_object, json_array}

# Create a simple object
var obj = json_object()
obj.add_string("name", "Alice")
obj.add_number("age", 30.0)
obj.add_bool("active", true)

val json = obj.to_string()
# Result: {"name":"Alice","age":30,"active":true}
```

### Nested Structures

```simple
use data.json.{json_object, json_array}

# Create nested object with arrays
var user = json_object()
user.add_string("username", "alice")
user.add_number("id", 123.0)

# Add hobbies array
var hobbies = json_array()
hobbies.push_string("reading")
hobbies.push_string("coding")
hobbies.push_string("hiking")
user.add_array("hobbies", hobbies)

# Add address object
var address = json_object()
address.add_string("city", "Seattle")
address.add_string("country", "USA")
user.add_object("address", address)

val json = user.to_string()
```

**Result (compact):**
```json
{"username":"alice","id":123,"hobbies":["reading","coding","hiking"],"address":{"city":"Seattle","country":"USA"}}
```

### Pretty Printing

```simple
val pretty = user.to_pretty_string()
print pretty
```

**Result:**
```json
{
  "username": "alice",
  "id": 123,
  "hobbies": [
    "reading",
    "coding",
    "hiking"
  ],
  "address": {
    "city": "Seattle",
    "country": "USA"
  }
}
```

### Null Values

```simple
var obj = json_object()
obj.add_string("name", "Bob")
obj.add_null("email")  # Explicitly null field

val json = obj.to_string()
# Result: {"name":"Bob","email":null}
```

### Arrays of Objects

```simple
var users_array = json_array()

var user1 = json_object()
user1.add_string("name", "Alice")
user1.add_number("age", 30.0)
users_array.push_object(user1)

var user2 = json_object()
user2.add_string("name", "Bob")
user2.add_number("age", 25.0)
users_array.push_object(user2)

val json = users_array.to_string()
# Result: [{"name":"Alice","age":30},{"name":"Bob","age":25}]
```

### Special Characters and Escaping

```simple
var obj = json_object()
obj.add_string("message", "Hello\nWorld!")
obj.add_string("path", "C:\\Users\\Alice")
obj.add_string("quote", "She said \"Hi\"")

val json = obj.to_string()
# Result: {"message":"Hello\nWorld!","path":"C:\\Users\\Alice","quote":"She said \"Hi\""}
```

The JSON module properly escapes:
- Backslash: `\` → `\\`
- Quote: `"` → `\"`
- Newline: `\n` → `\\n`
- Carriage return: `\r` → `\\r`
- Tab: `\t` → `\\t`
- Backspace: `\b` → `\\b`
- Form feed: `\f` → `\\f`

### Integration with Context Pack

```simple
use data.json.{json_object, json_array}
use tooling.context_pack.ContextPack

# Create a context pack
var pack = ContextPack::new("my_module")

# Export as JSON
match pack.to_json():
    Ok(json):
        print json
    Err(e):
        print "Error: {e}"

# Export as compact JSON
match pack.to_json_compact():
    Ok(json):
        # Send to LLM API
        send_to_llm(json)
    Err(e):
        print "Error: {e}"
```

## TODOs Removed

### 1. context_pack.spl (Line 8)
**Before:**
```simple
# TODO: [compiler][P1] Add JSON serialization to stdlib
# Stubbed for Phase 2
```

**After:**
```simple
use data.json.{json_object, json_array, JsonObject, JsonArray}
```

### 2. context_pack.spl (Line 65-69)
**Before:**
```simple
# TODO: [stdlib][P1] Add JSON serialization library
# Export as JSON (for LLM API consumption)
fn to_json() -> Result<text, text>:
    # Stub: Needs serde/JSON library
    Err("JSON serialization not yet implemented")
```

**After:**
```simple
# Export as JSON (for LLM API consumption)
fn to_json() -> Result<text, text>:
    var obj = json_object()
    obj.add_string("target", self.target)
    obj.add_number("symbol_count", self.symbol_count as f64)
    # ... full implementation
    Ok(obj.to_pretty_string())
```

## Files Modified/Created

1. **simple/std_lib/src/data/json.spl** (NEW - 300 lines)
   - JsonValue enum with 6 variants
   - JsonObject builder with 8 methods
   - JsonArray builder with 8 methods
   - 4 convenience functions
   - String escaping and formatting utilities

2. **simple/std_lib/src/data/__init__.spl** (NEW)
   - Data module entry point
   - Exports JSON module

3. **simple/std_lib/src/__init__.spl**
   - Added: `pub use data.*`
   - Registered data module in stdlib

4. **simple/std_lib/src/tooling/context_pack.spl**
   - Removed 2 JSON TODOs
   - Implemented `to_json()` method (45 lines)
   - Implemented `to_json_compact()` method (45 lines)
   - Added import: `use data.json.{json_object, json_array, JsonObject, JsonArray}`

## Implementation Details

### Pure Simple Implementation

The JSON module is implemented entirely in Simple without FFI:
- **Advantages:**
  - No external dependencies
  - Portable across all platforms
  - Easy to understand and maintain
  - No FFI overhead

- **Trade-offs:**
  - Manual string building (vs serde_json optimization)
  - No JSON parsing yet (serialization only)
  - Manual escape handling

### String Escaping

All strings are properly escaped according to JSON spec:
```simple
fn escape_string(s: text) -> text:
    var result = ""
    var i = 0
    while i < s.len():
        val c = s.char_at(i)
        if c == '\\':
            result = result + "\\\\"
        elif c == '"':
            result = result + "\\\""
        elif c == '\n':
            result = result + "\\n"
        # ... etc
    result
```

### Number Formatting

Numbers are formatted intelligently:
- Whole numbers: `30` (no decimal point)
- Decimals: `3.14` (with decimal point)

```simple
fn number_to_string(n: f64) -> text:
    val int_val = n as i64
    if (int_val as f64) == n:
        "{int_val}"  # Whole number
    else:
        "{n}"        # Decimal
```

### Pretty Printing

Pretty printing uses indentation with 2 spaces per level:
```simple
fn to_string_internal(indent: u64, pretty: bool) -> text:
    # ... builds output with repeat_string("  ", indent)
```

## API Design Decisions

### Builder Pattern

Chose builder pattern for ergonomic API:
```simple
# Good: Chainable, clear
var obj = json_object()
obj.add_string("name", "Alice")
obj.add_number("age", 30.0)

# Alternative (not chosen): Manual JsonValue construction
var obj = JsonValue.Object([
    ("name", JsonValue.String("Alice")),
    ("age", JsonValue.Number(30.0))
])
```

### Mutation Methods

Used `me` (mutable self) for builder methods:
```simple
pub me add_string(key: text, value: text)
pub me push_string(value: text)
```

This allows incremental construction without copying.

### Result Type for Context Pack

Context pack methods return `Result<text, text>`:
```simple
fn to_json() -> Result<text, text>
```

This maintains consistency with error handling patterns, even though current implementation always succeeds. Future enhancements (size limits, validation) can use the error path.

## Performance Characteristics

**Time Complexity:**
- Object construction: O(n) where n = number of fields
- Array construction: O(n) where n = number of elements
- String escaping: O(n) where n = string length
- Serialization: O(n) where n = total JSON nodes

**Space Complexity:**
- O(n) for storing the JSON structure
- O(m) for output string where m = serialized size

**No allocations during serialization** - uses string concatenation which may reallocate.

## Limitations and Future Work

### Current Limitations

1. **Serialization only** - No JSON parsing/deserialization yet
2. **No streaming** - Builds entire JSON in memory
3. **String concatenation** - Could be optimized with string builder
4. **Limited number formats** - Only f64, no i64/u64 direct support

### Future Enhancements

1. **JSON Parsing** - Add deserialization support
   ```simple
   fn parse_json(text: text) -> Result<JsonValue, text>
   ```

2. **Streaming API** - For large JSON documents
   ```simple
   struct JsonWriter:
       fn start_object()
       fn add_field(key: text)
       fn end_object()
   ```

3. **Derive Macros** - Auto-generate JSON serialization for structs
   ```simple
   #[derive(JsonSerialize)]
   struct User:
       name: text
       age: i32
   ```

4. **Direct Type Conversions** - Support for more Simple types
   ```simple
   obj.add_i64("count", 42)
   obj.add_option("maybe", Some("value"))
   ```

5. **Pretty Print Options** - Configurable indentation
   ```simple
   obj.to_pretty_string_with_indent(4)  # 4 spaces
   ```

6. **FFI Integration** - Optional serde_json backend for performance
   ```simple
   #[cfg(feature = "serde_json")]
   fn to_json_fast() -> text
   ```

## Benefits

1. **Type Safety**: Compile-time checking of JSON construction
2. **Ergonomic API**: Builder pattern for easy construction
3. **Proper Escaping**: Automatic string escaping for security
4. **Pretty Printing**: Human-readable JSON output
5. **Pure Simple**: No FFI dependencies, portable
6. **Extensible**: Easy to add new value types
7. **LLM Integration**: Unblocks context pack export for AI tools

## Impact

**TODOs Removed:** 2 P1 TODOs
**New API Surface:** 3 types, 24 methods, 4 convenience functions
**Lines of Code:** ~300 lines (json.spl)
**Functions Unblocked:**
- `context_pack.to_json()` - Export context packs as JSON
- `context_pack.to_json_compact()` - Compact JSON export
- Any future tooling requiring JSON serialization

## Example: Context Pack JSON Output

```simple
use tooling.context_pack.ContextPack

var pack = ContextPack::new("my_module")
# ... populate pack ...

match pack.to_json():
    Ok(json):
        print json
    Err(e):
        print "Error: {e}"
```

**Output:**
```json
{
  "target": "my_module",
  "symbol_count": 10,
  "types": [
    "User",
    "Config"
  ],
  "functions": [
    {
      "name": "init",
      "is_public": true,
      "is_async": false,
      "params": [
        {
          "name": "config",
          "type": "Config"
        }
      ],
      "return_type": "Result<User, Error>"
    }
  ],
  "imports": [
    "core.result.Result",
    "core.option.Option"
  ]
}
```

## Related Modules

**JSON Implementation:**
- `simple/std_lib/src/data/json.spl` - JSON serialization (300 lines)

**Integration:**
- `simple/std_lib/src/tooling/context_pack.spl` - LLM context packs
- Future: Config files, API responses, log formatting

**Core Dependencies:**
- `core.option.Option` - For optional fields
- `core.result.Result` - For error handling
- `core.string.*` - String operations (char_at, etc.)

## Testing Recommendations

1. **Basic serialization tests**
   - Empty objects/arrays
   - Single field/element
   - Multiple fields/elements

2. **Nesting tests**
   - Objects in objects
   - Arrays in arrays
   - Mixed nesting

3. **Escaping tests**
   - Special characters
   - Unicode
   - Control characters

4. **Number formatting tests**
   - Whole numbers
   - Decimals
   - Large numbers
   - Negative numbers

5. **Pretty printing tests**
   - Indentation levels
   - Newlines
   - Nested structures

6. **Integration tests**
   - Context pack export
   - Round-trip with parser (future)

## Conclusion

The JSON serialization library is now fully implemented and integrated into the stdlib. This removes 2 P1 TODOs and enables critical LLM tooling features like context pack export. The pure Simple implementation provides a solid foundation that can be extended with parsing, streaming, and FFI optimization in the future.

**Next recommended steps:**
1. Add unit tests for JSON module
2. Implement JSON parsing/deserialization
3. Add derive macros for automatic serialization
4. Consider FFI integration with serde_json for performance-critical use cases
