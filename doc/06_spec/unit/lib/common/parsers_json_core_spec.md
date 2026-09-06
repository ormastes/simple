# JSON Core Coverage Specification

> Purpose: Prove that JSON Types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 98 | 98 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON Core Coverage Specification

Purpose: Prove that JSON Types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-JSON-CORE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/unit/lib/common/parsers_json_core_spec.spl` |
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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

#### nested object parsing (regression: json-parser-nested-object-nil)

#### parses a directly-nested object, one level deep

- parses a directly-nested object, one level deep
- Verify: parses a directly-nested object, one level deep
   - Expected: json_is_object(result) is true
   - Expected: json_is_object(inner) is true
   - Expected: json_to_number(json_object_get(inner, "b")) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a directly-nested object, one level deep")
step("Verify: parses a directly-nested object, one level deep")
val text = "{" + "\"a\": " + "{" + "\"b\": 1" + "}" + "}"
val result = json_parse(text)
expect(json_is_object(result)).to_equal(true)
val inner = json_object_get(result, "a")
expect(json_is_object(inner)).to_equal(true)
# json_parse always produces f64 numbers -- compare against a
# float literal, not an int literal (1 != 1.0 in this interpreter).
expect(json_to_number(json_object_get(inner, "b"))).to_equal(1.0)
```

</details>

#### parses a directly-nested object, two levels deep

- parses a directly-nested object, two levels deep
- Verify: parses a directly-nested object, two levels deep
   - Expected: json_is_object(result) is true
   - Expected: json_is_object(b) is true
   - Expected: json_to_number(json_object_get(b, "c")) equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a directly-nested object, two levels deep")
step("Verify: parses a directly-nested object, two levels deep")
val text = "{" + "\"a\": " + "{" + "\"b\": " + "{" + "\"c\": 2" + "}" + "}" + "}"
val result = json_parse(text)
expect(json_is_object(result)).to_equal(true)
val a = json_object_get(result, "a")
val b = json_object_get(a, "b")
expect(json_is_object(b)).to_equal(true)
expect(json_to_number(json_object_get(b, "c"))).to_equal(2.0)
```

</details>

#### parses object-in-array-in-object

- parses object-in-array-in-object
- Verify: parses object-in-array-in-object
   - Expected: json_is_object(result) is true
   - Expected: items.len() equals `1`
   - Expected: json_to_number(json_object_get(items[0], "id")) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses object-in-array-in-object")
step("Verify: parses object-in-array-in-object")
val text = "{" + "\"items\": [" + "{" + "\"id\": 1" + "}" + "]" + "}"
val result = json_parse(text)
expect(json_is_object(result)).to_equal(true)
val items = json_to_array(json_object_get(result, "items"))
expect(items.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(json_to_number(json_object_get(items[0], "id"))).to_equal(1.0)
```

</details>

#### parses the bitbucket-shaped source/branch/name fixture

- parses the bitbucket-shaped source/branch/name fixture
- Verify: parses the bitbucket-shaped source/branch/name fixture
   - Expected: json_is_object(result) is true
   - Expected: json_is_object(branch) is true
   - Expected: json_to_string(json_object_get(branch, "name")) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the bitbucket-shaped source/branch/name fixture")
step("Verify: parses the bitbucket-shaped source/branch/name fixture")
val text = "{" + "\"source\": " + "{" + "\"branch\": " + "{" + "\"name\": \"x\"" + "}" + "}" + "}"
val result = json_parse(text)
expect(json_is_object(result)).to_equal(true)
val source = json_object_get(result, "source")
val branch = json_object_get(source, "branch")
expect(json_is_object(branch)).to_equal(true)
expect(json_to_string(json_object_get(branch, "name"))).to_equal("x")
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
step("serializes number")
step("Verify: serializes number")
val result = json_serialize(json_number(42))
expect(result).to_contain("42")
```

</details>

#### serializes an integral number without a fraction suffix

- serializes an integral number without a fraction suffix
- Verify: serializes an integral number without a fraction suffix
   - Expected: json_serialize(json_parse("42")) equals `42`
   - Expected: json_serialize(json_number(42)) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes an integral number without a fraction suffix")
step("Verify: serializes an integral number without a fraction suffix")
# Reproduce: the parser stores every number as f64, so `42` used to
# re-emit as `42.0` (llm_caret_json_parse_nil_contract_and_any_option_wrap_2026-08-25).
expect(json_serialize(json_parse("42"))).to_equal("42")
expect(json_serialize(json_number(42))).to_equal("42")
```

</details>

#### keeps integer formatting across zero, negative, and exponent forms

- keeps integer formatting across zero, negative, and exponent forms
- Verify: keeps integer formatting across zero, negative, and exponent forms
   - Expected: json_serialize(json_parse("0")) equals `0`
   - Expected: json_serialize(json_parse("-1")) equals `-1`
   - Expected: json_serialize(json_parse("1e3")) equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps integer formatting across zero, negative, and exponent forms")
step("Verify: keeps integer formatting across zero, negative, and exponent forms")
expect(json_serialize(json_parse("0"))).to_equal("0")
expect(json_serialize(json_parse("-1"))).to_equal("-1")
expect(json_serialize(json_parse("1e3"))).to_equal("1000")
```

</details>

#### keeps a fractional number fractional

- keeps a fractional number fractional
- Verify: keeps a fractional number fractional
   - Expected: json_serialize(json_parse("1.5")) equals `1.5`
   - Expected: json_serialize(json_number(2.5)) equals `2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a fractional number fractional")
step("Verify: keeps a fractional number fractional")
expect(json_serialize(json_parse("1.5"))).to_equal("1.5")
expect(json_serialize(json_number(2.5))).to_equal("2.5")
```

</details>

#### formats integers inside nested arrays and objects

- formats integers inside nested arrays and objects
- Verify: formats integers inside nested arrays and objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats integers inside nested arrays and objects")
step("Verify: formats integers inside nested arrays and objects")
val src = "{\"items\":[1,2.5,-3],\"n\":{\"a\":0" + "}" + "}"
expect(json_serialize(json_parse(src))).to_equal(
    "{\"items\":[1,2.5,-3],\"n\":{\"a\":0" + "}" + "}"
)
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
step("passes plain text through")
step("Verify: passes plain text through")
val result = escape_json("simple")
expect(result).to_equal("simple")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 98 |
| Active scenarios | 98 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3cf4436879a4a5da499478281c9e22f607d0eed8e5631c35112580bb9b965f48`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3cf4436879a4a5da499478281c9e22f607d0eed8e5631c35112580bb9b965f48`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3cf4436879a4a5da499478281c9e22f607d0eed8e5631c35112580bb9b965f48`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/parsers_json_core_spec.spl
mirror: doc/06_spec/unit/lib/common/parsers_json_core_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/parsers_json_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/parsers_json_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/parsers_json_core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/parsers_json_core_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates null value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/parsers_json_core_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates boolean true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/parsers_json_core_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates boolean false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
