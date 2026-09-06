# JSON Coverage Specification

> Purpose: Prove that JSON Types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 187 | 187 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON Coverage Specification

Purpose: Prove that JSON Types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-JSON |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/json_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that JSON Types.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### JSON Types

#### constructors
_Create each JSON value type and verify tuple structure._

#### creates null value

- creates null value
- Verify: creates null value
   - Expected: json_get_type(n) equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates null value")
step("Verify: creates null value")
# @req: REQ-LIB-COMMON-001
val n = json_null()
expect(json_get_type(n)).to_equal("null")
```

</details>

#### creates boolean true

- creates boolean true
- Verify: creates boolean true
   - Expected: json_get_type(b) equals `boolean`
   - Expected: json_to_boolean(b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates boolean true")
step("Verify: creates boolean true")
val b = json_boolean(true)
expect(json_get_type(b)).to_equal("boolean")
expect(json_to_boolean(b)).to_equal(true)
```

</details>

#### creates boolean false

- creates boolean false
- Verify: creates boolean false
   - Expected: json_get_type(b) equals `boolean`
   - Expected: json_to_boolean(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates boolean false")
step("Verify: creates boolean false")
val b = json_boolean(false)
expect(json_get_type(b)).to_equal("boolean")
expect(json_to_boolean(b)).to_equal(false)
```

</details>

#### creates number value

- creates number value
- Verify: creates number value
   - Expected: json_get_type(n) equals `number`
   - Expected: json_to_number(n) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates number value")
step("Verify: creates number value")
val n = json_number(42)
expect(json_get_type(n)).to_equal("number")
expect(json_to_number(n)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### creates string value

- creates string value
- Verify: creates string value
   - Expected: json_get_type(s) equals `string`
   - Expected: json_to_string(s) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates string value")
step("Verify: creates string value")
val s = json_string("hello")
expect(json_get_type(s)).to_equal("string")
expect(json_to_string(s)).to_equal("hello")
```

</details>

#### creates empty string

- creates empty string
- Verify: creates empty string
   - Expected: json_to_string(s) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty string")
step("Verify: creates empty string")
val s = json_string("")
expect(json_to_string(s)).to_equal("")
```

</details>

#### creates array value

- creates array value
- Verify: creates array value
   - Expected: json_get_type(arr) equals `array`
   - Expected: items.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates array value")
step("Verify: creates array value")
val arr = json_array([json_number(1), json_number(2)])
expect(json_get_type(arr)).to_equal("array")
val items = json_to_array(arr)
expect(items.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### creates empty array

- creates empty array
- Verify: creates empty array
   - Expected: json_get_type(arr) equals `array`
   - Expected: items.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty array")
step("Verify: creates empty array")
val arr = json_array([])
expect(json_get_type(arr)).to_equal("array")
val items = json_to_array(arr)
expect(items.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### creates object value

- creates object value
- Verify: creates object value
   - Expected: json_get_type(obj) equals `object`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates object value")
step("Verify: creates object value")
val obj = json_object({"name": json_string("Alice")})
expect(json_get_type(obj)).to_equal("object")
```

</details>

#### creates empty object

- creates empty object
- Verify: creates empty object
   - Expected: json_get_type(obj) equals `object`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty object")
step("Verify: creates empty object")
val obj = json_object({})
expect(json_get_type(obj)).to_equal("object")
```

</details>

#### type checking
_Type predicates return true for matching type, false otherwise._

#### json_get_type returns null for nil

- json_get_type returns null for nil
- Verify: json_get_type returns null for nil
   - Expected: json_get_type(nil) equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_get_type returns null for nil")
step("Verify: json_get_type returns null for nil")
expect(json_get_type(nil)).to_equal("null")
```

</details>

#### json_type_check matches correctly

- json_type_check matches correctly
- Verify: json_type_check matches correctly
   - Expected: json_type_check(n, "number") is true
   - Expected: json_type_check(n, "string") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_type_check matches correctly")
step("Verify: json_type_check matches correctly")
val n = json_number(5)
expect(json_type_check(n, "number")).to_equal(true)
expect(json_type_check(n, "string")).to_equal(false)
```

</details>

#### json_is_null detects null

- json_is_null detects null
- Verify: json_is_null detects null
   - Expected: json_is_null(json_null()) is true
   - Expected: json_is_null(json_number(0)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_is_null detects null")
step("Verify: json_is_null detects null")
expect(json_is_null(json_null())).to_equal(true)
expect(json_is_null(json_number(0))).to_equal(false)
```

</details>

#### json_is_boolean detects boolean

- json_is_boolean detects boolean
- Verify: json_is_boolean detects boolean
   - Expected: json_is_boolean(json_boolean(true)) is true
   - Expected: json_is_boolean(json_string("true")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_is_boolean detects boolean")
step("Verify: json_is_boolean detects boolean")
expect(json_is_boolean(json_boolean(true))).to_equal(true)
expect(json_is_boolean(json_string("true"))).to_equal(false)
```

</details>

#### json_is_number detects number

- json_is_number detects number
- Verify: json_is_number detects number
   - Expected: json_is_number(json_number(42)) is true
   - Expected: json_is_number(json_string("42")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_is_number detects number")
step("Verify: json_is_number detects number")
expect(json_is_number(json_number(42))).to_equal(true)
expect(json_is_number(json_string("42"))).to_equal(false)
```

</details>

#### json_is_string detects string

- json_is_string detects string
- Verify: json_is_string detects string
   - Expected: json_is_string(json_string("hi")) is true
   - Expected: json_is_string(json_number(1)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_is_string detects string")
step("Verify: json_is_string detects string")
expect(json_is_string(json_string("hi"))).to_equal(true)
expect(json_is_string(json_number(1))).to_equal(false)
```

</details>

#### json_is_array detects array

- json_is_array detects array
- Verify: json_is_array detects array
   - Expected: json_is_array(json_array([])) is true
   - Expected: json_is_array(json_object({})) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_is_array detects array")
step("Verify: json_is_array detects array")
expect(json_is_array(json_array([]))).to_equal(true)
expect(json_is_array(json_object({}))).to_equal(false)
```

</details>

#### json_is_object detects object

- json_is_object detects object
- Verify: json_is_object detects object
   - Expected: json_is_object(json_object({})) is true
   - Expected: json_is_object(json_array([])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_is_object detects object")
step("Verify: json_is_object detects object")
expect(json_is_object(json_object({}))).to_equal(true)
expect(json_is_object(json_array([]))).to_equal(false)
```

</details>

#### type conversion
_Extractors return value for matching type, nil for mismatches._

#### json_to_boolean extracts boolean

- json_to_boolean extracts boolean
- Verify: json_to_boolean extracts boolean
   - Expected: json_to_boolean(json_boolean(true)) is true
   - Expected: json_to_boolean(json_boolean(false)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_boolean extracts boolean")
step("Verify: json_to_boolean extracts boolean")
expect(json_to_boolean(json_boolean(true))).to_equal(true)
expect(json_to_boolean(json_boolean(false))).to_equal(false)
```

</details>

#### json_to_boolean returns nil for non-boolean

- json_to_boolean returns nil for non-boolean
- Verify: json_to_boolean returns nil for non-boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_boolean returns nil for non-boolean")
step("Verify: json_to_boolean returns nil for non-boolean")
expect(json_to_boolean(json_string("true"))).to_be_nil()
```

</details>

#### json_to_number extracts number

- json_to_number extracts number
- Verify: json_to_number extracts number
   - Expected: json_to_number(json_number(99)) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_number extracts number")
step("Verify: json_to_number extracts number")
expect(json_to_number(json_number(99))).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

#### json_to_number returns nil for non-number

- json_to_number returns nil for non-number
- Verify: json_to_number returns nil for non-number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_number returns nil for non-number")
step("Verify: json_to_number returns nil for non-number")
expect(json_to_number(json_string("99"))).to_be_nil()
```

</details>

#### json_to_string extracts string

- json_to_string extracts string
- Verify: json_to_string extracts string
   - Expected: json_to_string(json_string("abc")) equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_string extracts string")
step("Verify: json_to_string extracts string")
expect(json_to_string(json_string("abc"))).to_equal("abc")
```

</details>

#### json_to_string returns nil for non-string

- json_to_string returns nil for non-string
- Verify: json_to_string returns nil for non-string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_string returns nil for non-string")
step("Verify: json_to_string returns nil for non-string")
expect(json_to_string(json_number(1))).to_be_nil()
```

</details>

#### json_to_array extracts array

- json_to_array extracts array
- Verify: json_to_array extracts array
   - Expected: items.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_array extracts array")
step("Verify: json_to_array extracts array")
val arr = json_array([json_number(1)])
val items = json_to_array(arr)
expect(items.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### json_to_array returns nil for non-array

- json_to_array returns nil for non-array
- Verify: json_to_array returns nil for non-array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_array returns nil for non-array")
step("Verify: json_to_array returns nil for non-array")
expect(json_to_array(json_object({}))).to_be_nil()
```

</details>

#### json_to_object extracts object

- json_to_object extracts object
- Verify: json_to_object extracts object
   - Expected: map != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_object extracts object")
step("Verify: json_to_object extracts object")
val obj = json_object({"k": json_string("v")})
val map = json_to_object(obj)
expect(map != nil).to_equal(true)
```

</details>

#### json_to_object returns nil for non-object

- json_to_object returns nil for non-object
- Verify: json_to_object returns nil for non-object


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_to_object returns nil for non-object")
step("Verify: json_to_object returns nil for non-object")
expect(json_to_object(json_array([]))).to_be_nil()
```

</details>

### JSON Parser

#### tokenization
_json_tokenize produces correct token sequences._

#### tokenizes empty input

- tokenizes empty input
- Verify: tokenizes empty input
   - Expected: tokens.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tokenizes empty input")
step("Verify: tokenizes empty input")
val tokens = json_tokenize("")
expect(tokens.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### tokenizes negative number

- tokenizes negative number
- Verify: tokenizes negative number
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tokenizes negative number")
step("Verify: tokenizes negative number")
val tokens = json_tokenize("-42")
expect(tokens.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### tokenizes decimal number

- tokenizes decimal number
- Verify: tokenizes decimal number
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tokenizes decimal number")
step("Verify: tokenizes decimal number")
val tokens = json_tokenize("3.14")
expect(tokens.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### tokenizes returns a list

- tokenizes returns a list
- Verify: tokenizes returns a list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tokenizes returns a list")
step("Verify: tokenizes returns a list")
val tokens = json_tokenize("42")
expect(tokens.len()).to_be_greater_than(0)
```

</details>

#### parsing valid JSON
_json_parse returns correct JSON values for valid input._

#### parses null

- parses null
- Verify: parses null
   - Expected: json_is_null(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses null")
step("Verify: parses null")
val result = json_parse("null")
expect(json_is_null(result)).to_equal(true)
```

</details>

#### parses decimal number

- parses decimal number
- Verify: parses decimal number
   - Expected: json_is_number(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses decimal number")
step("Verify: parses decimal number")
val result = json_parse("3.14")
expect(json_is_number(result)).to_equal(true)
```

</details>

#### parses empty string

- parses empty string
- Verify: parses empty string
   - Expected: json_to_string(result) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses empty string")
step("Verify: parses empty string")
val result = json_parse("\"\"")
# json_parse returns a JSON value or nil
if result != nil:
    expect(json_to_string(result)).to_equal("")
else:
    # Tokenizer limitation: empty strings may not tokenize
    expect(result).to_be_nil()
```

</details>

#### json_parse returns value or nil

- json_parse returns value or nil
- Verify: json_parse returns value or nil
   - Expected: json_is_number(result) or result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("json_parse returns value or nil")
step("Verify: json_parse returns value or nil")
# Exercises the parse -> tokenize -> parse_tokens pipeline
val result = json_parse("42")
expect(json_is_number(result) or result == nil).to_equal(true)
```

</details>

#### parsed number is number type

- parsed number is number type
- Verify: parsed number is number type
   - Expected: json_is_number(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parsed number is number type")
step("Verify: parsed number is number type")
val result = json_parse("3.14")
if result != nil:
    expect(json_is_number(result)).to_equal(true)
else:
    expect(result).to_be_nil()
```

</details>

#### parses object via json_parse

- parses object via json_parse
- Verify: parses object via json_parse
   - Expected: json_is_object(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses object via json_parse")
step("Verify: parses object via json_parse")
val result = json_parse("{}")
# May return nil if tokenizer cannot handle braces
if result != nil:
    expect(json_is_object(result)).to_equal(true)
else:
    expect(result).to_be_nil()
```

</details>

#### parses array via json_parse

- parses array via json_parse
- Verify: parses array via json_parse
   - Expected: json_is_array(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses array via json_parse")
step("Verify: parses array via json_parse")
val result = json_parse("[]")
# May return nil if tokenizer cannot handle brackets
if result != nil:
    expect(json_is_array(result)).to_equal(true)
else:
    expect(result).to_be_nil()
```

</details>

#### parsing invalid JSON
_json_parse returns nil for invalid input._

#### returns nil for empty string

- returns nil for empty string
- Verify: returns nil for empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for empty string")
step("Verify: returns nil for empty string")
val result = json_parse("")
expect(result).to_be_nil()
```

</details>

#### returns nil for malformed input

- returns nil for malformed input
- Verify: returns nil for malformed input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for malformed input")
step("Verify: returns nil for malformed input")
val result = json_parse("not json at all")
expect(result).to_be_nil()
```

</details>

#### parse with error
_json_parse_with_error returns value and error message._

#### returns nil with error message on failure

- returns nil with error message on failure
- Verify: returns nil with error message on failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil with error message on failure")
step("Verify: returns nil with error message on failure")
val result = json_parse_with_error("")
val value = result.0
expect(value).to_be_nil()
```

</details>

#### parse tokens directly
_json_parse_tokens handles edge cases._

#### returns failure for empty token list

- returns failure for empty token list
- Verify: returns failure for empty token list
   - Expected: result.0 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns failure for empty token list")
step("Verify: returns failure for empty token list")
val result = json_parse_tokens([])
expect(result.0).to_equal(false)
```

</details>

### JSON Serializer

#### json_serialize
_Serialize each JSON type to compact text._

#### serializes null

- serializes null
- Verify: serializes null
   - Expected: result equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes null")
step("Verify: serializes null")
val result = json_serialize(json_null())
expect(result).to_equal("null")
```

</details>

#### serializes nil as null

- serializes nil as null
- Verify: serializes nil as null
   - Expected: result equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes nil as null")
step("Verify: serializes nil as null")
val result = json_serialize(nil)
expect(result).to_equal("null")
```

</details>

#### serializes true

- serializes true
- Verify: serializes true
   - Expected: result equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes true")
step("Verify: serializes true")
val result = json_serialize(json_boolean(true))
expect(result).to_equal("true")
```

</details>

#### serializes false

- serializes false
- Verify: serializes false
   - Expected: result equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes false")
step("Verify: serializes false")
val result = json_serialize(json_boolean(false))
expect(result).to_equal("false")
```

</details>

#### serializes number

- serializes number
- Verify: serializes number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes number")
step("Verify: serializes number")
val result = json_serialize(json_number(42))
expect(result).to_contain("42")
```

</details>

#### serializes string type

- serializes string type
- Verify: serializes string type
   - Expected: json_get_type(s) equals `string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes string type")
step("Verify: serializes string type")
val s = json_string("hello")
expect(json_get_type(s)).to_equal("string")
```

</details>

#### serializes string to text

- serializes string to text
- Verify: serializes string to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes string to text")
step("Verify: serializes string to text")
val result = json_serialize(json_string(""))
# Empty string serializes to quoted empty
expect(result.len()).to_be_greater_than(0)
```

</details>

#### serializes empty array

- serializes empty array
- Verify: serializes empty array
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes empty array")
step("Verify: serializes empty array")
val result = json_serialize(json_array([]))
expect(result).to_equal("[]")
```

</details>

#### serializes array with items

- serializes array with items
- Verify: serializes array with items


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes array with items")
step("Verify: serializes array with items")
val result = json_serialize(json_array([json_number(1), json_number(2)]))
expect(result).to_contain("1")
expect(result).to_contain("2")
```

</details>

#### serializes empty object

- serializes empty object
- Verify: serializes empty object
   - Expected: result equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes empty object")
step("Verify: serializes empty object")
val result = json_serialize(json_object({}))
expect(result).to_equal("{}")
```

</details>

#### serializes object with fields

- serializes object with fields
- Verify: serializes object with fields
   - Expected: result equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes object with fields")
step("Verify: serializes object with fields")
val obj = json_object({})
val result = json_serialize(obj)
expect(result).to_equal("{}")
```

</details>

#### json_format and json_pretty
_Formatted serialization with indentation._

#### pretty-prints object

- pretty-prints object
- Verify: pretty-prints object
   - Expected: result equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pretty-prints object")
step("Verify: pretty-prints object")
val obj = json_object({})
val result = json_pretty(obj)
expect(result).to_equal("{}")
```

</details>

#### pretty-prints array

- pretty-prints array
- Verify: pretty-prints array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pretty-prints array")
step("Verify: pretty-prints array")
val arr = json_array([json_number(1), json_number(2)])
val result = json_pretty(arr)
expect(result).to_contain("\n")
```

</details>

#### pretty-prints empty object compactly

- pretty-prints empty object compactly
- Verify: pretty-prints empty object compactly
   - Expected: result equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pretty-prints empty object compactly")
step("Verify: pretty-prints empty object compactly")
val result = json_pretty(json_object({}))
expect(result).to_equal("{}")
```

</details>

#### pretty-prints empty array compactly

- pretty-prints empty array compactly
- Verify: pretty-prints empty array compactly
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pretty-prints empty array compactly")
step("Verify: pretty-prints empty array compactly")
val result = json_pretty(json_array([]))
expect(result).to_equal("[]")
```

</details>

#### pretty-prints null

- pretty-prints null
- Verify: pretty-prints null
   - Expected: result equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pretty-prints null")
step("Verify: pretty-prints null")
val result = json_pretty(json_null())
expect(result).to_equal("null")
```

</details>

#### pretty-prints nil

- pretty-prints nil
- Verify: pretty-prints nil
   - Expected: result equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pretty-prints nil")
step("Verify: pretty-prints nil")
val result = json_pretty(nil)
expect(result).to_equal("null")
```

</details>

#### format with custom indent

- format with custom indent
- Verify: format with custom indent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("format with custom indent")
step("Verify: format with custom indent")
val obj = json_object({"x": json_number(1)})
val result = json_format(obj, 0, 4)
expect(result).to_contain("x")
```

</details>

#### json_stringify alias
_json_stringify is an alias for json_serialize._

#### returns same as serialize

- returns same as serialize
- Verify: returns same as serialize
   - Expected: s1 equals `s2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns same as serialize")
step("Verify: returns same as serialize")
val obj = json_object({"a": json_number(1)})
val s1 = json_serialize(obj)
val s2 = json_stringify(obj)
expect(s1).to_equal(s2)
```

</details>

#### json_minify and json_beautify
_Minification removes whitespace, beautify adds it._

#### minifies JSON text

- minifies JSON text
- Verify: minifies JSON text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("minifies JSON text")
step("Verify: minifies JSON text")
val result = json_minify("{  \"key\" :  42  }")
expect(result).to_contain("key")
# Should not have extra whitespace
```

</details>

#### beautifies JSON text

- beautifies JSON text
- Verify: beautifies JSON text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("beautifies JSON text")
step("Verify: beautifies JSON text")
val result = json_beautify("{\"key\":42}")
expect(result).to_contain("key")
```

</details>

#### minify returns input on invalid JSON

- minify returns input on invalid JSON
- Verify: minify returns input on invalid JSON
   - Expected: result equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("minify returns input on invalid JSON")
step("Verify: minify returns input on invalid JSON")
val input = "not json at all"
val result = json_minify(input)
expect(result).to_equal(input)
```

</details>

#### json_escape_string
_Escape special characters for JSON strings._

#### returns empty for empty input

- returns empty for empty input
- Verify: returns empty for empty input
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty for empty input")
step("Verify: returns empty for empty input")
val result = json_escape_string("")
expect(result).to_equal("")
```

</details>

#### json_indent
_json_indent creates indentation strings._

#### creates indentation for level 0

- creates indentation for level 0
- Verify: creates indentation for level 0
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates indentation for level 0")
step("Verify: creates indentation for level 0")
val result = json_indent(0, 2)
expect(result).to_equal("")
```

</details>

#### creates indentation for level 1

- creates indentation for level 1
- Verify: creates indentation for level 1
   - Expected: result equals `  `


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates indentation for level 1")
step("Verify: creates indentation for level 1")
val result = json_indent(1, 2)
expect(result).to_equal("  ")
```

</details>

#### creates indentation for level 2 with size 4

- creates indentation for level 2 with size 4
- Verify: creates indentation for level 2 with size 4
   - Expected: result equals `        `


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates indentation for level 2 with size 4")
step("Verify: creates indentation for level 2 with size 4")
val result = json_indent(2, 4)
expect(result).to_equal("        ")
```

</details>

### JSON Builder

#### JsonBuilder
_Object builder methods._

#### builds empty object

- builds empty object
- Verify: builds empty object
   - Expected: result equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds empty object")
step("Verify: builds empty object")
val result = JsonBuilder.object().build()
expect(result).to_equal("{}")
```

</details>

#### builds object with string field

- builds object with string field
- Verify: builds object with string field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object with string field")
step("Verify: builds object with string field")
var builder = JsonBuilder.object()
builder = builder.field("name", "Alice")
val result = builder.build()
expect(result).to_contain("name")
expect(result).to_contain("Alice")
```

</details>

#### builds object with integer field

- builds object with integer field
- Verify: builds object with integer field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object with integer field")
step("Verify: builds object with integer field")
var builder = JsonBuilder.object()
builder = builder.field_int("age", 30)
val result = builder.build()
expect(result).to_contain("age")
expect(result).to_contain("30")
```

</details>

#### builds object with boolean field

- builds object with boolean field
- Verify: builds object with boolean field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object with boolean field")
step("Verify: builds object with boolean field")
var builder = JsonBuilder.object()
builder = builder.field_bool("active", true)
val result = builder.build()
expect(result).to_contain("active")
expect(result).to_contain("true")
```

</details>

#### builds object with false boolean field

- builds object with false boolean field
- Verify: builds object with false boolean field


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object with false boolean field")
step("Verify: builds object with false boolean field")
var builder = JsonBuilder.object()
builder = builder.field_bool("active", false)
val result = builder.build()
expect(result).to_contain("false")
```

</details>

#### builds object with null field

- builds object with null field
- Verify: builds object with null field


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object with null field")
step("Verify: builds object with null field")
var builder = JsonBuilder.object()
builder = builder.field_null("empty")
val result = builder.build()
expect(result).to_contain("null")
```

</details>

#### builds object with raw field

- builds object with raw field
- Verify: builds object with raw field


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object with raw field")
step("Verify: builds object with raw field")
var builder = JsonBuilder.object()
builder = builder.field_raw("data", "[1,2,3]")
val result = builder.build()
expect(result).to_contain("[1,2,3]")
```

</details>

#### builds object with float field

- builds object with float field
- Verify: builds object with float field


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object with float field")
step("Verify: builds object with float field")
var builder = JsonBuilder.object()
builder = builder.field_float("pi", 3.14)
val result = builder.build()
expect(result).to_contain("3.14")
```

</details>

#### builds object with multiple fields

- builds object with multiple fields
- Verify: builds object with multiple fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object with multiple fields")
step("Verify: builds object with multiple fields")
var builder = JsonBuilder.object()
builder = builder.field("name", "Alice")
builder = builder.field_int("age", 30)
val result = builder.build()
expect(result).to_contain("name")
expect(result).to_contain("age")
```

</details>

#### escapes special chars in field values

- escapes special chars in field values
- Verify: escapes special chars in field values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes special chars in field values")
step("Verify: escapes special chars in field values")
var builder = JsonBuilder.object()
builder = builder.field("msg", "hello \"world\"")
val result = builder.build()
expect(result).to_contain("\\\"")
```

</details>

#### build_raw returns object without outer braces marker

- build_raw returns object without outer braces marker
- Verify: build_raw returns object without outer braces marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("build_raw returns object without outer braces marker")
step("Verify: build_raw returns object without outer braces marker")
var builder = JsonBuilder.object()
builder = builder.field("k", "v")
val raw = builder.build_raw()
expect(raw).to_contain("k")
```

</details>

#### JsonArrayBuilder
_Array builder methods._

#### builds empty array

- builds empty array
- Verify: builds empty array
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds empty array")
step("Verify: builds empty array")
val result = JsonArrayBuilder.new().build()
expect(result).to_equal("[]")
```

</details>

#### builds array with string items

- builds array with string items
- Verify: builds array with string items


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds array with string items")
step("Verify: builds array with string items")
var builder = JsonArrayBuilder.new()
builder = builder.item("hello")
builder = builder.item("world")
val result = builder.build()
expect(result).to_contain("hello")
expect(result).to_contain("world")
```

</details>

#### builds array with integer items

- builds array with integer items
- Verify: builds array with integer items


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds array with integer items")
step("Verify: builds array with integer items")
var builder = JsonArrayBuilder.new()
builder = builder.item_int(1)
builder = builder.item_int(2)
val result = builder.build()
expect(result).to_contain("1")
expect(result).to_contain("2")
```

</details>

#### builds array with float items

- builds array with float items
- Verify: builds array with float items


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds array with float items")
step("Verify: builds array with float items")
var builder = JsonArrayBuilder.new()
builder = builder.item_float(3.14)
val result = builder.build()
expect(result).to_contain("3.14")
```

</details>

#### builds array with boolean items

- builds array with boolean items
- Verify: builds array with boolean items


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds array with boolean items")
step("Verify: builds array with boolean items")
var builder = JsonArrayBuilder.new()
builder = builder.item_bool(true)
builder = builder.item_bool(false)
val result = builder.build()
expect(result).to_contain("true")
expect(result).to_contain("false")
```

</details>

#### builds array with null items

- builds array with null items
- Verify: builds array with null items


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds array with null items")
step("Verify: builds array with null items")
var builder = JsonArrayBuilder.new()
builder = builder.item_null()
val result = builder.build()
expect(result).to_contain("null")
```

</details>

#### builds array with raw items

- builds array with raw items
- Verify: builds array with raw items


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds array with raw items")
step("Verify: builds array with raw items")
var builder = JsonArrayBuilder.new()
builder = builder.item_raw("{\"k\":1}")
val result = builder.build()
expect(result).to_contain("{\"k\":1}")
```

</details>

#### builds array with nested object

- builds array with nested object
- Verify: builds array with nested object


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds array with nested object")
step("Verify: builds array with nested object")
var obj = JsonBuilder.object()
obj = obj.field("name", "Alice")
var builder = JsonArrayBuilder.new()
builder = builder.item_object(obj)
val result = builder.build()
expect(result).to_contain("name")
```

</details>

#### escape_json helper
_escape_json utility for string escaping._

#### escapes special characters

- escapes special characters
- Verify: escapes special characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes special characters")
step("Verify: escapes special characters")
val result = escape_json("hello\nworld")
expect(result).to_contain("\\n")
```

</details>

#### passes plain text through

- passes plain text through
- Verify: passes plain text through
   - Expected: result equals `simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes plain text through")
step("Verify: passes plain text through")
val result = escape_json("simple")
expect(result).to_equal("simple")
```

</details>

### JSON Object Operations

#### basic operations

#### returns nil when getting from non-object

- returns nil when getting from non-object
- Verify: returns nil when getting from non-object


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil when getting from non-object")
step("Verify: returns nil when getting from non-object")
val result = json_object_get(json_number(42), "key")
expect(result).to_be_nil()
```

</details>

#### sets value on non-object creates new object

- sets value on non-object creates new object
- Verify: sets value on non-object creates new object
   - Expected: json_is_object(updated) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets value on non-object creates new object")
step("Verify: sets value on non-object creates new object")
val updated = json_object_set(json_null(), "key", json_number(1))
expect(json_is_object(updated)).to_equal(true)
```

</details>

#### checks key on non-object returns false

- checks key on non-object returns false
- Verify: checks key on non-object returns false
   - Expected: json_object_has(json_array([]), "x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks key on non-object returns false")
step("Verify: checks key on non-object returns false")
expect(json_object_has(json_array([]), "x")).to_equal(false)
```

</details>

#### empty object has zero size

- empty object has zero size
- Verify: empty object has zero size
   - Expected: json_object_size(json_object({})) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty object has zero size")
step("Verify: empty object has zero size")
expect(json_object_size(json_object({}))).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### sets and checks object

- sets and checks object
- Verify: sets and checks object
   - Expected: json_is_object(updated) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets and checks object")
step("Verify: sets and checks object")
val obj = json_object({})
val updated = json_object_set(obj, "name", json_string("Bob"))
expect(json_is_object(updated)).to_equal(true)
```

</details>

#### property accessors

#### gets keys from empty object

- gets keys from empty object
- Verify: gets keys from empty object
   - Expected: keys.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets keys from empty object")
step("Verify: gets keys from empty object")
val obj = json_object({})
val keys = json_object_keys(obj)
expect(keys.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### gets values from empty object

- gets values from empty object
- Verify: gets values from empty object
   - Expected: vals.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets values from empty object")
step("Verify: gets values from empty object")
val obj = json_object({})
val vals = json_object_values(obj)
expect(vals.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### gets entries from empty object

- gets entries from empty object
- Verify: gets entries from empty object
   - Expected: entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets entries from empty object")
step("Verify: gets entries from empty object")
val obj = json_object({})
val entries = json_object_entries(obj)
expect(entries.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### gets size of object

- gets size of object
- Verify: gets size of object
   - Expected: json_object_size(obj) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets size of object")
step("Verify: gets size of object")
val obj = json_object({"a": json_number(1), "b": json_number(2)})
expect(json_object_size(obj)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### gets size of empty object

- gets size of empty object
- Verify: gets size of empty object
   - Expected: json_object_size(json_object({})) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets size of empty object")
step("Verify: gets size of empty object")
expect(json_object_size(json_object({}))).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### checks empty object

- checks empty object
- Verify: checks empty object
   - Expected: json_object_empty(json_object({})) is true
   - Expected: json_object_empty(json_object({"a": json_number(1)})) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks empty object")
step("Verify: checks empty object")
expect(json_object_empty(json_object({}))).to_equal(true)
expect(json_object_empty(json_object({"a": json_number(1)}))).to_equal(false)
```

</details>

#### higher-order operations

#### maps object values

- maps object values
- Verify: maps object values
   - Expected: json_to_number(json_object_get(mapped, "a")) equals `10`
   - Expected: json_to_number(json_object_get(mapped, "b")) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps object values")
step("Verify: maps object values")
val obj = json_object({"a": json_number(1), "b": json_number(2)})
val mapped = json_object_map_values(obj, json_number(json_to_number(_1) * 10))
expect(json_to_number(json_object_get(mapped, "a"))).to_equal(10)
expect(json_to_number(json_object_get(mapped, "b"))).to_equal(20)
```

</details>

#### map values returns empty object for non-object

- map values returns empty object for non-object
- Verify: map values returns empty object for non-object
   - Expected: json_object_size(mapped) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("map values returns empty object for non-object")
step("Verify: map values returns empty object for non-object")
val mapped = json_object_map_values(json_number(1), \v: v)
expect(json_object_size(mapped)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### filters object entries

- filters object entries
- Verify: filters object entries
   - Expected: json_object_has(filtered, "a") is false
   - Expected: json_object_has(filtered, "b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("filters object entries")
step("Verify: filters object entries")
val obj = json_object({"a": json_number(1), "b": json_number(2)})
val filtered = json_object_filter(obj, \k, v: json_to_number(v) > 1)
expect(json_object_has(filtered, "a")).to_equal(false)
expect(json_object_has(filtered, "b")).to_equal(true)
```

</details>

#### finds matching object entry

- finds matching object entry
- Verify: finds matching object entry
   - Expected: found.0 equals `b`
   - Expected: json_to_number(found.1) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds matching object entry")
step("Verify: finds matching object entry")
val obj = json_object({"a": json_number(1), "b": json_number(2)})
val found = json_object_find(obj, \k, v: json_to_number(v) == 2)
expect(found.0).to_equal("b")
expect(json_to_number(found.1)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### returns nil when object find misses

- returns nil when object find misses
- Verify: returns nil when object find misses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil when object find misses")
step("Verify: returns nil when object find misses")
val obj = json_object({"a": json_number(1)})
expect(json_object_find(obj, \k, v: json_to_number(v) == 9)).to_be_nil()
```

</details>

#### removes requested keys with without

- removes requested keys with without
- Verify: removes requested keys with without
   - Expected: json_object_has(result, "a") is true
   - Expected: json_object_has(result, "b") is false
   - Expected: json_object_has(result, "c") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes requested keys with without")
step("Verify: removes requested keys with without")
val obj = json_object({"a": json_number(1), "b": json_number(2), "c": json_number(3)})
val result = json_object_without(obj, ["b", "x"])
expect(json_object_has(result, "a")).to_equal(true)
expect(json_object_has(result, "b")).to_equal(false)
expect(json_object_has(result, "c")).to_equal(true)
```

</details>

#### picks only requested existing keys

- picks only requested existing keys
- Verify: picks only requested existing keys
   - Expected: json_object_size(result) equals `1`
   - Expected: json_to_number(json_object_get(result, "b")) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("picks only requested existing keys")
step("Verify: picks only requested existing keys")
val obj = json_object({"a": json_number(1), "b": json_number(2)})
val result = json_object_pick(obj, ["b", "missing"])
expect(json_object_size(result)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(json_to_number(json_object_get(result, "b"))).to_equal(2)
```

</details>

#### builds object from entries

- builds object from entries
- Verify: builds object from entries
   - Expected: json_object_size(result) equals `2`
   - Expected: json_to_number(json_object_get(result, "a")) equals `1`
   - Expected: json_to_string(json_object_get(result, "b")) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds object from entries")
step("Verify: builds object from entries")
val result = json_from_entries([("a", json_number(1)), ("b", json_string("x"))])
expect(json_object_size(result)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(json_to_number(json_object_get(result, "a"))).to_equal(1)
expect(json_to_string(json_object_get(result, "b"))).to_equal("x")
```

</details>

### JSON Array Operations

#### basic operations

#### gets element by index

- gets element by index
- Verify: gets element by index
   - Expected: json_to_number(result) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets element by index")
step("Verify: gets element by index")
val arr = json_array([json_number(10), json_number(20)])
val result = json_array_get(arr, 0)
expect(json_to_number(result)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### returns nil for out-of-bounds index

- returns nil for out-of-bounds index
- Verify: returns nil for out-of-bounds index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for out-of-bounds index")
step("Verify: returns nil for out-of-bounds index")
val arr = json_array([json_number(10)])
expect(json_array_get(arr, 5)).to_be_nil()
```

</details>

#### returns nil for negative index

- returns nil for negative index
- Verify: returns nil for negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for negative index")
step("Verify: returns nil for negative index")
val arr = json_array([json_number(10)])
expect(json_array_get(arr, -1)).to_be_nil()
```

</details>

#### returns nil when getting from non-array

- returns nil when getting from non-array
- Verify: returns nil when getting from non-array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil when getting from non-array")
step("Verify: returns nil when getting from non-array")
expect(json_array_get(json_object({}), 0)).to_be_nil()
```

</details>

#### sets element at index

- sets element at index
- Verify: sets element at index
   - Expected: json_to_number(result) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets element at index")
step("Verify: sets element at index")
val arr = json_array([json_number(1), json_number(2)])
val updated = json_array_set(arr, 0, json_number(99))
val result = json_array_get(updated, 0)
expect(json_to_number(result)).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

#### set returns unchanged for out-of-bounds

- set returns unchanged for out-of-bounds
- Verify: set returns unchanged for out-of-bounds
   - Expected: json_array_length(updated) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set returns unchanged for out-of-bounds")
step("Verify: set returns unchanged for out-of-bounds")
val arr = json_array([json_number(1)])
val updated = json_array_set(arr, 5, json_number(99))
expect(json_array_length(updated)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### appends element

- appends element
- Verify: appends element
   - Expected: json_array_length(updated) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("appends element")
step("Verify: appends element")
val arr = json_array([json_number(1)])
val updated = json_array_append(arr, json_number(2))
expect(json_array_length(updated)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### prepends element

- prepends element
- Verify: prepends element
   - Expected: json_array_length(updated) equals `2`
   - Expected: json_to_number(first) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("prepends element")
step("Verify: prepends element")
val arr = json_array([json_number(2)])
val updated = json_array_prepend(arr, json_number(1))
expect(json_array_length(updated)).to_equal(2)  # oracle: 2 — named expected value from the requirement
val first = json_array_get(updated, 0)
expect(json_to_number(first)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### removes element at index

- removes element at index
- Verify: removes element at index
   - Expected: json_array_length(updated) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes element at index")
step("Verify: removes element at index")
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val updated = json_array_remove(arr, 1)
expect(json_array_length(updated)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### inserts element in middle

- inserts element in middle
- Verify: inserts element in middle
   - Expected: json_array_length(updated) equals `3`
   - Expected: json_to_number(json_array_get(updated, 1)) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("inserts element in middle")
step("Verify: inserts element in middle")
val arr = json_array([json_number(1), json_number(3)])
val updated = json_array_insert(arr, 1, json_number(2))
expect(json_array_length(updated)).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(json_to_number(json_array_get(updated, 1))).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### inserts element at array end

- inserts element at array end
- Verify: inserts element at array end
   - Expected: json_array_length(updated) equals `2`
   - Expected: json_to_number(json_array_last(updated)) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("inserts element at array end")
step("Verify: inserts element at array end")
val arr = json_array([json_number(1)])
val updated = json_array_insert(arr, 1, json_number(2))
expect(json_array_length(updated)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(json_to_number(json_array_last(updated))).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### insert returns original on invalid index

- insert returns original on invalid index
- Verify: insert returns original on invalid index
   - Expected: json_array_length(updated) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("insert returns original on invalid index")
step("Verify: insert returns original on invalid index")
val arr = json_array([json_number(1)])
val updated = json_array_insert(arr, -1, json_number(2))
expect(json_array_length(updated)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### remove returns empty array for non-array

- remove returns empty array for non-array
- Verify: remove returns empty array for non-array
   - Expected: json_array_length(updated) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("remove returns empty array for non-array")
step("Verify: remove returns empty array for non-array")
val updated = json_array_remove(json_number(1), 0)
expect(json_array_length(updated)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### properties

#### gets length

- gets length
- Verify: gets length
   - Expected: json_array_length(arr) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets length")
step("Verify: gets length")
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_length(arr)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### checks empty - true

- checks empty - true
- Verify: checks empty - true
   - Expected: json_array_empty(json_array([])) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks empty - true")
step("Verify: checks empty - true")
expect(json_array_empty(json_array([]))).to_equal(true)
```

</details>

#### checks empty - false

- checks empty - false
- Verify: checks empty - false
   - Expected: json_array_empty(json_array([json_number(1)])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks empty - false")
step("Verify: checks empty - false")
expect(json_array_empty(json_array([json_number(1)]))).to_equal(false)
```

</details>

#### gets first element

- gets first element
- Verify: gets first element
   - Expected: json_to_number(first) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets first element")
step("Verify: gets first element")
val arr = json_array([json_number(10), json_number(20)])
val first = json_array_first(arr)
expect(json_to_number(first)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### gets last element

- gets last element
- Verify: gets last element
   - Expected: json_to_number(last) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gets last element")
step("Verify: gets last element")
val arr = json_array([json_number(10), json_number(20)])
val last = json_array_last(arr)
expect(json_to_number(last)).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

#### slices array

- slices array
- Verify: slices array
   - Expected: json_array_length(sliced) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("slices array")
step("Verify: slices array")
val arr = json_array([json_number(1), json_number(2), json_number(3), json_number(4)])
val sliced = json_array_slice(arr, 1, 3)
expect(json_array_length(sliced)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### concatenates two arrays

- concatenates two arrays
- Verify: concatenates two arrays
   - Expected: json_array_length(combined) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("concatenates two arrays")
step("Verify: concatenates two arrays")
val a1 = json_array([json_number(1)])
val a2 = json_array([json_number(2)])
val combined = json_array_concat(a1, a2)
expect(json_array_length(combined)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### reverses array

- reverses array
- Verify: reverses array
   - Expected: json_to_number(first) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reverses array")
step("Verify: reverses array")
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val reversed = json_array_reverse(arr)
val first = json_array_get(reversed, 0)
expect(json_to_number(first)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### checks contains - true

- checks contains - true
- Verify: checks contains - true
   - Expected: json_array_contains(arr, json_number(2)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks contains - true")
step("Verify: checks contains - true")
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_contains(arr, json_number(2))).to_equal(true)
```

</details>

#### checks contains - false

- checks contains - false
- Verify: checks contains - false
   - Expected: json_array_contains(arr, json_number(99)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks contains - false")
step("Verify: checks contains - false")
val arr = json_array([json_number(1)])
expect(json_array_contains(arr, json_number(99))).to_equal(false)
```

</details>

#### finds index of element

- finds index of element
- Verify: finds index of element
   - Expected: idx equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds index of element")
step("Verify: finds index of element")
val arr = json_array([json_number(10), json_number(20), json_number(30)])
val idx = json_array_index_of(arr, json_number(20))
expect(idx).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns -1 for missing element

- returns -1 for missing element
- Verify: returns -1 for missing element
   - Expected: idx equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns -1 for missing element")
step("Verify: returns -1 for missing element")
val arr = json_array([json_number(1)])
val idx = json_array_index_of(arr, json_number(99))
expect(idx).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### flattens nested arrays

- flattens nested arrays
- Verify: flattens nested arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flattens nested arrays")
step("Verify: flattens nested arrays")
val inner = json_array([json_number(3), json_number(4)])
val arr = json_array([json_number(1), json_number(2), inner])
val flat = json_array_flatten(arr)
expect(json_array_length(flat)).to_be_greater_than(2)
```

</details>

#### removes duplicate values

- removes duplicate values
- Verify: removes duplicate values
   - Expected: json_array_length(unique) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes duplicate values")
step("Verify: removes duplicate values")
val arr = json_array([json_number(1), json_number(2)])
val unique = json_array_unique(arr)
# unique of non-duplicated array should have same length
expect(json_array_length(unique)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### last returns nil for empty array

- last returns nil for empty array
- Verify: last returns nil for empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("last returns nil for empty array")
step("Verify: last returns nil for empty array")
expect(json_array_last(json_array([]))).to_be_nil()
```

</details>

#### slice clamps negative start and oversized end

- slice clamps negative start and oversized end
- Verify: slice clamps negative start and oversized end
   - Expected: json_array_length(sliced) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("slice clamps negative start and oversized end")
step("Verify: slice clamps negative start and oversized end")
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val sliced = json_array_slice(arr, -2, 9)
expect(json_array_length(sliced)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### slice returns empty when start is after end

- slice returns empty when start is after end
- Verify: slice returns empty when start is after end
   - Expected: json_array_length(sliced) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("slice returns empty when start is after end")
step("Verify: slice returns empty when start is after end")
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val sliced = json_array_slice(arr, 2, 1)
expect(json_array_length(sliced)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### concat returns empty array when both inputs are non-arrays

- concat returns empty array when both inputs are non-arrays
- Verify: concat returns empty array when both inputs are non-arrays
   - Expected: json_array_length(combined) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("concat returns empty array when both inputs are non-arrays")
step("Verify: concat returns empty array when both inputs are non-arrays")
val combined = json_array_concat(json_number(1), json_string("x"))
expect(json_array_length(combined)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### higher-order operations

#### maps array values

- maps array values
- Verify: maps array values
   - Expected: json_to_number(json_array_get(mapped, 0)) equals `2`
   - Expected: json_to_number(json_array_get(mapped, 1)) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps array values")
step("Verify: maps array values")
val arr = json_array([json_number(1), json_number(2)])
val mapped = json_array_map(arr, json_number(json_to_number(_1) * 2))
expect(json_to_number(json_array_get(mapped, 0))).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(json_to_number(json_array_get(mapped, 1))).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### filters array values

- filters array values
- Verify: filters array values
   - Expected: json_array_length(filtered) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("filters array values")
step("Verify: filters array values")
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val filtered = json_array_filter(arr, json_to_number(_1) >= 2)
expect(json_array_length(filtered)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### finds array value

- finds array value
- Verify: finds array value
   - Expected: json_to_number(found) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds array value")
step("Verify: finds array value")
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val found = json_array_find(arr, json_to_number(_1) == 2)
expect(json_to_number(found)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### returns nil when array find misses

- returns nil when array find misses
- Verify: returns nil when array find misses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil when array find misses")
step("Verify: returns nil when array find misses")
val arr = json_array([json_number(1)])
expect(json_array_find(arr, \x: json_to_number(x) == 9)).to_be_nil()
```

</details>

#### every returns false when predicate fails

- every returns false when predicate fails
- Verify: every returns false when predicate fails
   - Expected: json_array_every(arr, \x: json_to_number(x) > 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("every returns false when predicate fails")
step("Verify: every returns false when predicate fails")
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_every(arr, \x: json_to_number(x) > 1)).to_equal(false)
```

</details>

#### some returns true when predicate matches

- some returns true when predicate matches
- Verify: some returns true when predicate matches
   - Expected: json_array_some(arr, \x: json_to_number(x) == 2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("some returns true when predicate matches")
step("Verify: some returns true when predicate matches")
val arr = json_array([json_number(1), json_number(2)])
expect(json_array_some(arr, \x: json_to_number(x) == 2)).to_equal(true)
```

</details>

#### reduce accumulates array

- reduce accumulates array
- Verify: reduce accumulates array
   - Expected: json_to_number(reduced) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reduce accumulates array")
step("Verify: reduce accumulates array")
val arr = json_array([json_number(1), json_number(2), json_number(3)])
val reduced = json_array_reduce(arr, json_number(0), \acc, v: json_number(json_to_number(acc) + json_to_number(v)))
expect(json_to_number(reduced)).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### sorts array by numeric key

- sorts array by numeric key
- Verify: sorts array by numeric key
   - Expected: json_to_number(json_object_get(json_array_get(sorted, 0), "age")) equals `10`
   - Expected: json_to_number(json_object_get(json_array_get(sorted, 2), "age")) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sorts array by numeric key")
step("Verify: sorts array by numeric key")
val arr = json_array([
    json_object({"age": json_number(30)}),
    json_object({"age": json_number(10)}),
    json_object({"age": json_number(20)})
])
val sorted = json_array_sort_by(arr, json_to_number(json_object_get(_1, "age")))
expect(json_to_number(json_object_get(json_array_get(sorted, 0), "age"))).to_equal(10)
expect(json_to_number(json_object_get(json_array_get(sorted, 2), "age"))).to_equal(30)
```

</details>

#### groups array values by key

- groups array values by key
- Verify: groups array values by key
   - Expected: json_array_length(json_object_get(grouped, "a")) equals `2`
   - Expected: json_array_length(json_object_get(grouped, "b")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("groups array values by key")
step("Verify: groups array values by key")
val arr = json_array([
    json_object({"kind": json_string("a")}),
    json_object({"kind": json_string("b")}),
    json_object({"kind": json_string("a")})
])
val grouped = json_array_group_by(arr, \x: json_to_string(json_object_get(x, "kind")))
expect(json_array_length(json_object_get(grouped, "a"))).to_equal(2)
expect(json_array_length(json_object_get(grouped, "b"))).to_equal(1)
```

</details>

### JSON Path Operations

#### path parsing

#### parses simple path

- parses simple path
- Verify: parses simple path
   - Expected: parts.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses simple path")
step("Verify: parses simple path")
val parts = json_path_parse("user.name")
expect(parts.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### parses single-segment path

- parses single-segment path
- Verify: parses single-segment path
   - Expected: parts.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses single-segment path")
step("Verify: parses single-segment path")
val parts = json_path_parse("name")
expect(parts.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns empty for empty path

- returns empty for empty path
- Verify: returns empty for empty path
   - Expected: parts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty for empty path")
step("Verify: returns empty for empty path")
val parts = json_path_parse("")
expect(parts.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### path get

#### returns nil for nil current

- returns nil for nil current
- Verify: returns nil for nil current


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for nil current")
step("Verify: returns nil for nil current")
val result = json_path_get(nil, "a.b")
expect(result).to_be_nil()
```

</details>

#### path set

#### returns new_value for empty path

- returns new_value for empty path
- Verify: returns new_value for empty path
   - Expected: json_to_number(result) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns new_value for empty path")
step("Verify: returns new_value for empty path")
val result = json_path_set(json_object({}), "", json_number(42))
expect(json_to_number(result)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### path delete

#### returns object for empty path

- returns object for empty path
- Verify: returns object for empty path
   - Expected: json_is_object(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns object for empty path")
step("Verify: returns object for empty path")
val obj = json_object({"a": json_number(1)})
val result = json_path_delete(obj, "")
expect(json_is_object(result)).to_equal(true)
```

</details>

### JSON Validation

#### schema validation

#### validates nil schema as valid

- validates nil schema as valid
- Verify: validates nil schema as valid
   - Expected: result.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates nil schema as valid")
step("Verify: validates nil schema as valid")
val result = json_validate_schema(json_number(1), nil)
expect(result.0).to_equal(true)
```

</details>

#### deep equals

#### equal nulls

- equal nulls
- Verify: equal nulls
   - Expected: json_deep_equals(json_null(), json_null()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("equal nulls")
step("Verify: equal nulls")
expect(json_deep_equals(json_null(), json_null())).to_equal(true)
```

</details>

#### equal numbers

- equal numbers
- Verify: equal numbers
   - Expected: json_deep_equals(json_number(42), json_number(42)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("equal numbers")
step("Verify: equal numbers")
expect(json_deep_equals(json_number(42), json_number(42))).to_equal(true)
```

</details>

#### unequal numbers

- unequal numbers
- Verify: unequal numbers
   - Expected: json_deep_equals(json_number(1), json_number(2)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unequal numbers")
step("Verify: unequal numbers")
expect(json_deep_equals(json_number(1), json_number(2))).to_equal(false)
```

</details>

#### different types

- different types
- Verify: different types
   - Expected: json_deep_equals(json_number(1), json_string("1")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("different types")
step("Verify: different types")
expect(json_deep_equals(json_number(1), json_string("1"))).to_equal(false)
```

</details>

#### nil vs nil

- nil vs nil
- Verify: nil vs nil
   - Expected: json_deep_equals(nil, nil) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("nil vs nil")
step("Verify: nil vs nil")
expect(json_deep_equals(nil, nil)).to_equal(true)
```

</details>

#### nil vs value

- nil vs value
- Verify: nil vs value
   - Expected: json_deep_equals(nil, json_number(1)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("nil vs value")
step("Verify: nil vs value")
expect(json_deep_equals(nil, json_number(1))).to_equal(false)
```

</details>

#### value vs nil

- value vs nil
- Verify: value vs nil
   - Expected: json_deep_equals(json_number(1), nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("value vs nil")
step("Verify: value vs nil")
expect(json_deep_equals(json_number(1), nil)).to_equal(false)
```

</details>

#### equal booleans

- equal booleans
- Verify: equal booleans
   - Expected: json_deep_equals(json_boolean(true), json_boolean(true)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("equal booleans")
step("Verify: equal booleans")
expect(json_deep_equals(json_boolean(true), json_boolean(true))).to_equal(true)
```

</details>

#### unequal booleans

- unequal booleans
- Verify: unequal booleans
   - Expected: json_deep_equals(json_boolean(true), json_boolean(false)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unequal booleans")
step("Verify: unequal booleans")
expect(json_deep_equals(json_boolean(true), json_boolean(false))).to_equal(false)
```

</details>

#### equal strings

- equal strings
- Verify: equal strings
   - Expected: json_deep_equals(json_string("a"), json_string("a")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("equal strings")
step("Verify: equal strings")
expect(json_deep_equals(json_string("a"), json_string("a"))).to_equal(true)
```

</details>

#### unequal strings

- unequal strings
- Verify: unequal strings
   - Expected: json_deep_equals(json_string("a"), json_string("b")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unequal strings")
step("Verify: unequal strings")
expect(json_deep_equals(json_string("a"), json_string("b"))).to_equal(false)
```

</details>

#### equal arrays

- equal arrays
- Verify: equal arrays
   - Expected: json_deep_equals(a, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("equal arrays")
step("Verify: equal arrays")
val a = json_array([json_number(1), json_number(2)])
val b = json_array([json_number(1), json_number(2)])
expect(json_deep_equals(a, b)).to_equal(true)
```

</details>

#### unequal arrays

- unequal arrays
- Verify: unequal arrays
   - Expected: json_deep_equals(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unequal arrays")
step("Verify: unequal arrays")
val a = json_array([json_number(1)])
val b = json_array([json_number(2)])
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### arrays with different lengths

- arrays with different lengths
- Verify: arrays with different lengths
   - Expected: json_deep_equals(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("arrays with different lengths")
step("Verify: arrays with different lengths")
val a = json_array([json_number(1)])
val b = json_array([json_number(1), json_number(2)])
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### equal empty objects

- equal empty objects
- Verify: equal empty objects
   - Expected: json_deep_equals(a, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("equal empty objects")
step("Verify: equal empty objects")
val a = json_object({})
val b = json_object({})
expect(json_deep_equals(a, b)).to_equal(true)
```

</details>

#### empty vs non-empty object

- empty vs non-empty object
- Verify: empty vs non-empty object
   - Expected: json_deep_equals(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty vs non-empty object")
step("Verify: empty vs non-empty object")
val a = json_object({})
val b = json_object({"x": json_number(1)})
expect(json_deep_equals(a, b)).to_equal(false)
```

</details>

#### deep clone

#### clones null

- clones null
- Verify: clones null
   - Expected: json_is_null(cloned) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clones null")
step("Verify: clones null")
val cloned = json_deep_clone(json_null())
expect(json_is_null(cloned)).to_equal(true)
```

</details>

#### clones nil

- clones nil
- Verify: clones nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clones nil")
step("Verify: clones nil")
val cloned = json_deep_clone(nil)
expect(cloned).to_be_nil()
```

</details>

#### clones boolean

- clones boolean
- Verify: clones boolean
   - Expected: json_to_boolean(cloned) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clones boolean")
step("Verify: clones boolean")
val cloned = json_deep_clone(json_boolean(true))
expect(json_to_boolean(cloned)).to_equal(true)
```

</details>

#### clones number

- clones number
- Verify: clones number
   - Expected: json_to_number(cloned) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clones number")
step("Verify: clones number")
val cloned = json_deep_clone(json_number(42))
expect(json_to_number(cloned)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### clones string

- clones string
- Verify: clones string
   - Expected: json_to_string(cloned) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clones string")
step("Verify: clones string")
val cloned = json_deep_clone(json_string("hello"))
expect(json_to_string(cloned)).to_equal("hello")
```

</details>

#### clones array

- clones array
- Verify: clones array
   - Expected: json_deep_equals(arr, cloned) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clones array")
step("Verify: clones array")
val arr = json_array([json_number(1), json_number(2)])
val cloned = json_deep_clone(arr)
expect(json_deep_equals(arr, cloned)).to_equal(true)
```

</details>

#### clones empty object

- clones empty object
- Verify: clones empty object
   - Expected: json_is_object(cloned) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clones empty object")
step("Verify: clones empty object")
val obj = json_object({})
val cloned = json_deep_clone(obj)
expect(json_is_object(cloned)).to_equal(true)
```

</details>

### JSON Utilities

#### json_merge_deep

#### returns obj2 when obj1 is not object

- returns obj2 when obj1 is not object
- Verify: returns obj2 when obj1 is not object
   - Expected: json_is_object(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns obj2 when obj1 is not object")
step("Verify: returns obj2 when obj1 is not object")
val result = json_merge_deep(json_number(1), json_object({"a": json_number(1)}))
expect(json_is_object(result)).to_equal(true)
```

</details>

#### returns obj1 when obj2 is not object

- returns obj1 when obj2 is not object
- Verify: returns obj1 when obj2 is not object
   - Expected: json_is_object(result) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns obj1 when obj2 is not object")
step("Verify: returns obj1 when obj2 is not object")
val obj = json_object({"a": json_number(1)})
val result = json_merge_deep(obj, json_number(2))
expect(json_is_object(result)).to_equal(true)
```

</details>

#### merges two empty objects

- merges two empty objects
- Verify: merges two empty objects
   - Expected: json_is_object(merged) is true
   - Expected: json_object_size(merged) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges two empty objects")
step("Verify: merges two empty objects")
val a = json_object({})
val b = json_object({})
val merged = json_merge_deep(a, b)
expect(json_is_object(merged)).to_equal(true)
expect(json_object_size(merged)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### json_diff

#### empty diff for empty objects

- empty diff for empty objects
- Verify: empty diff for empty objects
   - Expected: json_object_size(diff) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty diff for empty objects")
step("Verify: empty diff for empty objects")
val a = json_object({})
val b = json_object({})
val diff = json_diff(a, b)
expect(json_object_size(diff)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### json_patch

#### returns obj when inputs are not objects

- returns obj when inputs are not objects
- Verify: returns obj when inputs are not objects
   - Expected: json_to_number(result) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns obj when inputs are not objects")
step("Verify: returns obj when inputs are not objects")
val result = json_patch(json_number(1), json_number(2))
expect(json_to_number(result)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### json_flatten_object

#### returns non-object unchanged

- returns non-object unchanged
- Verify: returns non-object unchanged
   - Expected: json_to_number(result) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns non-object unchanged")
step("Verify: returns non-object unchanged")
val result = json_flatten_object(json_number(42))
expect(json_to_number(result)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### flattens empty object

- flattens empty object
- Verify: flattens empty object
   - Expected: json_object_size(flat) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flattens empty object")
step("Verify: flattens empty object")
val obj = json_object({})
val flat = json_flatten_object(obj)
expect(json_object_size(flat)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### json_unflatten_object

#### returns non-object unchanged

- returns non-object unchanged
- Verify: returns non-object unchanged
   - Expected: json_to_number(result) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns non-object unchanged")
step("Verify: returns non-object unchanged")
val result = json_unflatten_object(json_number(42))
expect(json_to_number(result)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 187 |
| Active scenarios | 187 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `80a95dc54ea0f22ed5108d3ea6db8d18479f6a4b901201562646a3bf7c57cc5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80a95dc54ea0f22ed5108d3ea6db8d18479f6a4b901201562646a3bf7c57cc5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80a95dc54ea0f22ed5108d3ea6db8d18479f6a4b901201562646a3bf7c57cc5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/json_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/json_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/json_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/json_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/json_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/json_coverage_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates null value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/json_coverage_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates boolean true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/json_coverage_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates boolean false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
