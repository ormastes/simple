# JSON Parser and Serializer Modules

Refactored from `json_parser_utils.spl` (2,240 lines) into 8 focused modules.

## Module Structure

| Module | Lines | Purpose |
|--------|-------|---------|
| `types.spl` | ~310 | Core constructors, type checking, type conversion |
| `parser.spl` | ~400 | Tokenization and parsing of JSON text |
| `serializer.spl` | ~250 | JSON serialization with formatting |
| `object_ops.spl` | ~320 | JSON object operations |
| `array_ops.spl` | ~650 | JSON array operations |
| `path_ops.spl` | ~120 | JSONPath-like navigation |
| `validation.spl` | ~140 | Schema validation and deep comparison |
| `utilities.spl` | ~150 | Advanced operations (merge, diff, flatten) |

## API Overview

### Types (`types.spl`)

**Constructors:**
- `json_null()` - Create null value
- `json_boolean(value)` - Create boolean value
- `json_number(value)` - Create number value
- `json_string(value)` - Create string value
- `json_array(values)` - Create array value
- `json_object(pairs)` - Create object value

**Type Checking:**
- `json_get_type(value)` - Get type name
- `json_type_check(value, type)` - Check type
- `json_is_null/boolean/number/string/array/object(value)` - Type predicates

**Type Conversion:**
- `json_to_boolean/number/string/array/object(value)` - Extract typed values

### Parser (`parser.spl`)

- `json_parse(text)` - Parse JSON text to value
- `json_parse_with_error(text)` - Parse with error message
- `json_tokenize(text)` - Tokenize JSON text
- `json_parse_tokens(tokens)` - Parse tokens to value

### Serializer (`serializer.spl`)

- `json_serialize(value)` - Serialize to compact JSON
- `json_pretty(value)` - Pretty-print with 2-space indent
- `json_format(value, level, size)` - Custom indentation
- `json_stringify(value)` - Alias for serialize
- `json_minify(text)` - Remove whitespace
- `json_beautify(text)` - Pretty-print text
- `json_escape_string(s)` - Escape string for JSON

### Object Operations (`object_ops.spl`)

**Basic:**
- `json_object_get(obj, key)` - Get value by key
- `json_object_set(obj, key, value)` - Set value
- `json_object_has(obj, key)` - Check if key exists
- `json_object_remove(obj, key)` - Remove key
- `json_object_keys(obj)` - Get all keys
- `json_object_values(obj)` - Get all values
- `json_object_entries(obj)` - Get key-value pairs

**Properties:**
- `json_object_size(obj)` - Number of keys
- `json_object_empty(obj)` - Check if empty
- `json_object_merge(obj1, obj2)` - Shallow merge

**Higher-Order:**
- `json_object_map_values(obj, fn)` - Transform values
- `json_object_filter(obj, fn)` - Filter entries
- `json_object_find(obj, fn)` - Find first match
- `json_object_without(obj, keys)` - Exclude keys
- `json_object_pick(obj, keys)` - Include only keys

**Utilities:**
- `json_from_entries(entries)` - Create object from pairs

### Array Operations (`array_ops.spl`)

**Basic:**
- `json_array_get(arr, index)` - Get element
- `json_array_set(arr, index, value)` - Set element
- `json_array_append(arr, value)` - Append element
- `json_array_prepend(arr, value)` - Prepend element
- `json_array_insert(arr, index, value)` - Insert element
- `json_array_remove(arr, index)` - Remove element

**Properties:**
- `json_array_length(arr)` - Get length
- `json_array_empty(arr)` - Check if empty
- `json_array_first(arr)` - Get first element
- `json_array_last(arr)` - Get last element
- `json_array_slice(arr, start, end)` - Get slice
- `json_array_concat(arr1, arr2)` - Concatenate arrays
- `json_array_reverse(arr)` - Reverse array

**Higher-Order:**
- `json_array_map(arr, fn)` - Transform elements
- `json_array_filter(arr, fn)` - Filter elements
- `json_array_find(arr, fn)` - Find first match
- `json_array_reduce(arr, init, fn)` - Reduce to value
- `json_array_every(arr, fn)` - Check all match
- `json_array_some(arr, fn)` - Check any match

**Search:**
- `json_array_contains(arr, value)` - Check if contains
- `json_array_index_of(arr, value)` - Find index

**Utilities:**
- `json_array_flatten(arr)` - Flatten one level
- `json_array_unique(arr)` - Remove duplicates
- `json_array_sort_by(arr, fn)` - Sort by key
- `json_array_group_by(arr, fn)` - Group by key

### Path Operations (`path_ops.spl`)

- `json_path_get(value, path)` - Get value at path (e.g., "user.name")
- `json_path_set(value, path, new_value)` - Set value at path
- `json_path_has(value, path)` - Check if path exists
- `json_path_delete(value, path)` - Delete value at path
- `json_path_parse(path)` - Parse path string

### Validation (`validation.spl`)

- `json_validate_schema(value, schema)` - Validate against schema
- `json_deep_equals(a, b)` - Deep equality comparison
- `json_deep_clone(value)` - Deep clone value

### Utilities (`utilities.spl`)

**Advanced Operations:**
- `json_merge_deep(obj1, obj2)` - Deep merge objects
- `json_diff(obj1, obj2)` - Find differences
- `json_patch(obj, patch)` - Apply patch
- `json_flatten_object(obj)` - Flatten to dotted keys
- `json_unflatten_object(obj)` - Unflatten dotted keys

## Usage Examples

### Basic Parsing and Serialization

```simple
# Parse JSON
val data = json_parse("{\"name\": \"Alice\", \"age\": 30}")

# Access values
val name = json_object_get(data, "name")  # json_string("Alice")
val age = json_object_get(data, "age")    # json_number(30)

# Serialize back
val json_text = json_serialize(data)      # Compact
val pretty_text = json_pretty(data)       # Pretty-printed
```

### Working with Objects

```simple
# Create object
var user = json_object({
    "name": json_string("Bob"),
    "age": json_number(25)
})

# Update
user = json_object_set(user, "email", json_string("bob@example.com"))

# Check and remove
if json_object_has(user, "temp"):
    user = json_object_remove(user, "temp")
```

### Working with Arrays

```simple
# Create array
var numbers = json_array([
    json_number(1),
    json_number(2),
    json_number(3)
])

# Transform
numbers = json_array_map(numbers, \x: json_number(json_to_number(x) * 2))

# Filter
numbers = json_array_filter(numbers, \x: json_to_number(x) > 3)
```

### Path Operations

```simple
# Nested access
val city = json_path_get(data, "user.address.city")

# Nested update
data = json_path_set(data, "user.age", json_number(31))

# Check nested path
if json_path_has(data, "user.settings.theme"):
    val theme = json_path_get(data, "user.settings.theme")
```

### Validation

```simple
# Define schema
val schema = json_object({
    "type": json_string("object"),
    "properties": json_object({
        "name": json_object({"type": json_string("string")}),
        "age": json_object({"type": json_string("number")})
    })
})

# Validate
val (valid, error) = json_validate_schema(user, schema)
if not valid:
    print "Validation error: {error}"
```

## Implementation Notes

- **Pure Simple:** No external dependencies or FFI
- **Immutable:** All operations return new values
- **Type-safe:** Tuple-based representation with type tags
- **Backward compatible:** Facade pattern preserves all original imports
- **Well-tested:** All functions covered by test suite

## Refactoring Details

- **Original:** `json_parser_utils.spl` (2,240 lines)
- **Facade:** `json_parser_utils.spl` (40 lines)
- **Modules:** 8 files (~2,400 lines total)
- **Pattern:** Import all submodules, export *
- **Backup:** `json_parser_utils.spl.backup`

## See Also

- Parent: `src/lib/common/json/` (facade)
- Tests: `test/std/json_parser_utils_spec.spl`
- Plan: `doc/report/stdlib_utils_refactoring_plan_2026-02-12.md`
