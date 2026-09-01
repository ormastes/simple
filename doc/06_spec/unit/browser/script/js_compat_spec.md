# JS Compat Spec

> Purpose: Prove that JS Compat - Number Parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JS Compat Spec

Purpose: Prove that JS Compat - Number Parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/browser/script/js_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that JS Compat - Number Parsing.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### JS Compat - Number Parsing

#### parses integer from string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses integer from string
- Verify: parses integer from string
   - Expected: js_parse_int("42") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses integer from string")
step("Verify: parses integer from string")
# @req: REQ-BROWSER-SCRIPT-001
expect(js_parse_int("42")).to_equal(42)
```

</details>

#### parses zero

- parses zero
- Verify: parses zero
   - Expected: js_parse_int("0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses zero")
step("Verify: parses zero")
expect(js_parse_int("0")).to_equal(0)
```

</details>

#### returns 0 for empty string

- returns 0 for empty string
- Verify: returns 0 for empty string
   - Expected: js_parse_int("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty string")
step("Verify: returns 0 for empty string")
expect(js_parse_int("")).to_equal(0)
```

</details>

#### parses float from string

- parses float from string
- Verify: parses float from string
   - Expected: result > 3.13 is true
   - Expected: result < 3.15 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses float from string")
step("Verify: parses float from string")
val result = js_parse_float("3.14")
expect(result > 3.13).to_equal(true)
expect(result < 3.15).to_equal(true)
```

</details>

#### returns 0.0 for empty float string

- returns 0.0 for empty float string
- Verify: returns 0.0 for empty float string
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0.0 for empty float string")
step("Verify: returns 0.0 for empty float string")
val result = js_parse_float("")
expect(result).to_equal(0.0)  # oracle: 0.0 — named expected value from the requirement
```

</details>

#### converts to string identity

- converts to string identity
- Verify: converts to string identity
   - Expected: js_to_string("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to string identity")
step("Verify: converts to string identity")
expect(js_to_string("hello")).to_equal("hello")
```

</details>

### JS Compat - Number Checks

#### is_finite for normal number

- is_finite for normal number
- Verify: is_finite for normal number
   - Expected: js_is_finite(42.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_finite for normal number")
step("Verify: is_finite for normal number")
expect(js_is_finite(42.0)).to_equal(true)
```

</details>

#### is_finite for zero

- is_finite for zero
- Verify: is_finite for zero
   - Expected: js_is_finite(0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_finite for zero")
step("Verify: is_finite for zero")
expect(js_is_finite(0.0)).to_equal(true)
```

</details>

### JS Compat - Math

#### floor rounds down

- floor rounds down
- Verify: floor rounds down
   - Expected: js_math_floor(3.7) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("floor rounds down")
step("Verify: floor rounds down")
expect(js_math_floor(3.7)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### floor negative rounds down

- floor negative rounds down
- Verify: floor negative rounds down
   - Expected: js_math_floor(-2.3) equals `-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("floor negative rounds down")
step("Verify: floor negative rounds down")
expect(js_math_floor(-2.3)).to_equal(-3)  # oracle: -3 — named expected value from the requirement
```

</details>

#### ceil rounds up

- ceil rounds up
- Verify: ceil rounds up
   - Expected: js_math_ceil(3.2) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ceil rounds up")
step("Verify: ceil rounds up")
expect(js_math_ceil(3.2)).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### round rounds to nearest

- round rounds to nearest
- Verify: round rounds to nearest
   - Expected: js_math_round(3.5) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round rounds to nearest")
step("Verify: round rounds to nearest")
expect(js_math_round(3.5)).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### round rounds down below 0.5

- round rounds down below 0.5
- Verify: round rounds down below 0.5
   - Expected: js_math_round(3.4) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round rounds down below 0.5")
step("Verify: round rounds down below 0.5")
expect(js_math_round(3.4)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### random returns value in range

- random returns value in range
- Verify: random returns value in range
   - Expected: r >= 0.0 is true
   - Expected: r < 1.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("random returns value in range")
step("Verify: random returns value in range")
val r = js_math_random()
expect(r >= 0.0).to_equal(true)
expect(r < 1.0).to_equal(true)
```

</details>

#### abs of positive

- abs of positive
- Verify: abs of positive
   - Expected: result equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abs of positive")
step("Verify: abs of positive")
val result = js_math_abs(5.0)
expect(result).to_equal(5.0)  # oracle: 5.0 — named expected value from the requirement
```

</details>

#### abs of negative

- abs of negative
- Verify: abs of negative
   - Expected: result equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abs of negative")
step("Verify: abs of negative")
val result = js_math_abs(-5.0)
expect(result).to_equal(5.0)  # oracle: 5.0 — named expected value from the requirement
```

</details>

#### min returns smaller

- min returns smaller
- Verify: min returns smaller
   - Expected: result equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("min returns smaller")
step("Verify: min returns smaller")
val result = js_math_min(3.0, 7.0)
expect(result).to_equal(3.0)  # oracle: 3.0 — named expected value from the requirement
```

</details>

#### max returns larger

- max returns larger
- Verify: max returns larger
   - Expected: result equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("max returns larger")
step("Verify: max returns larger")
val result = js_math_max(3.0, 7.0)
expect(result).to_equal(7.0)  # oracle: 7.0 — named expected value from the requirement
```

</details>

#### sqrt of 4

- sqrt of 4
- Verify: sqrt of 4
   - Expected: result > 1.99 is true
   - Expected: result < 2.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt of 4")
step("Verify: sqrt of 4")
val result = js_math_sqrt(4.0)
expect(result > 1.99).to_equal(true)
expect(result < 2.01).to_equal(true)
```

</details>

#### sqrt of 0

- sqrt of 0
- Verify: sqrt of 0
   - Expected: result equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt of 0")
step("Verify: sqrt of 0")
val result = js_math_sqrt(0.0)
expect(result).to_equal(0.0)  # oracle: 0.0 — named expected value from the requirement
```

</details>

#### pow integer exponent

- pow integer exponent
- Verify: pow integer exponent
   - Expected: result equals `1024.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pow integer exponent")
step("Verify: pow integer exponent")
val result = js_math_pow(2.0, 10.0)
expect(result).to_equal(1024.0)  # oracle: 1024.0 — named expected value from the requirement
```

</details>

#### pow zero exponent

- pow zero exponent
- Verify: pow zero exponent
   - Expected: result equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pow zero exponent")
step("Verify: pow zero exponent")
val result = js_math_pow(5.0, 0.0)
expect(result).to_equal(1.0)  # oracle: 1.0 — named expected value from the requirement
```

</details>

#### pi value

- pi value
- Verify: pi value
   - Expected: pi > 3.14 is true
   - Expected: pi < 3.15 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pi value")
step("Verify: pi value")
val pi = js_math_pi()
expect(pi > 3.14).to_equal(true)
expect(pi < 3.15).to_equal(true)
```

</details>

### JS Compat - String

#### splits string

- splits string
- Verify: splits string
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `a`
   - Expected: parts[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits string")
step("Verify: splits string")
val parts = js_string_split("a,b,c", ",")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(parts[0]).to_equal("a")
expect(parts[2]).to_equal("c")
```

</details>

#### joins array

- joins array
- Verify: joins array
   - Expected: result equals `x-y-z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins array")
step("Verify: joins array")
var arr: [text] = ["x", "y", "z"]
val result = js_string_join(arr, "-")
expect(result).to_equal("x-y-z")
```

</details>

#### trims whitespace

- trims whitespace
- Verify: trims whitespace
   - Expected: js_string_trim("  hi  ") equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims whitespace")
step("Verify: trims whitespace")
expect(js_string_trim("  hi  ")).to_equal("hi")
```

</details>

#### starts_with

- starts_with
- Verify: starts_with
   - Expected: js_string_starts_with("hello", "hel") is true
   - Expected: js_string_starts_with("hello", "xyz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts_with")
step("Verify: starts_with")
expect(js_string_starts_with("hello", "hel")).to_equal(true)
expect(js_string_starts_with("hello", "xyz")).to_equal(false)
```

</details>

#### ends_with

- ends_with
- Verify: ends_with
   - Expected: js_string_ends_with("hello", "llo") is true
   - Expected: js_string_ends_with("hello", "xyz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends_with")
step("Verify: ends_with")
expect(js_string_ends_with("hello", "llo")).to_equal(true)
expect(js_string_ends_with("hello", "xyz")).to_equal(false)
```

</details>

#### includes

- includes
- Verify: includes
   - Expected: js_string_includes("hello world", "world") is true
   - Expected: js_string_includes("hello world", "xyz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes")
step("Verify: includes")
expect(js_string_includes("hello world", "world")).to_equal(true)
expect(js_string_includes("hello world", "xyz")).to_equal(false)
```

</details>

#### replace

- replace
- Verify: replace
   - Expected: js_string_replace("hello world", "world", "there") equals `hello there`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replace")
step("Verify: replace")
expect(js_string_replace("hello world", "world", "there")).to_equal("hello there")
```

</details>

#### to_lower

- to_lower
- Verify: to_lower
   - Expected: js_string_to_lower("HELLO") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_lower")
step("Verify: to_lower")
expect(js_string_to_lower("HELLO")).to_equal("hello")
```

</details>

#### to_upper

- to_upper
- Verify: to_upper
   - Expected: js_string_to_upper("hello") equals `HELLO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_upper")
step("Verify: to_upper")
expect(js_string_to_upper("hello")).to_equal("HELLO")
```

</details>

### JS Compat - Array

#### push adds item

- push adds item
- Verify: push adds item
   - Expected: arr.len() equals `2`
   - Expected: arr[1] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push adds item")
step("Verify: push adds item")
var arr: [text] = ["a"]
js_array_push(arr, "b")
expect(arr.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(arr[1]).to_equal("b")
```

</details>

#### pop returns last item

- pop returns last item
- Verify: pop returns last item
   - Expected: popped equals `c`
   - Expected: arr.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pop returns last item")
step("Verify: pop returns last item")
var arr: [text] = ["a", "b", "c"]
val popped = js_array_pop(arr)
expect(popped).to_equal("c")
expect(arr.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### pop empty returns empty string

- pop empty returns empty string
- Verify: pop empty returns empty string
   - Expected: popped equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pop empty returns empty string")
step("Verify: pop empty returns empty string")
var arr: [text] = []
val popped = js_array_pop(arr)
expect(popped).to_equal("")
```

</details>

#### length returns count

- length returns count
- Verify: length returns count
   - Expected: js_array_length(arr) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("length returns count")
step("Verify: length returns count")
var arr: [text] = ["a", "b"]
expect(js_array_length(arr)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### index_of finds item

- index_of finds item
- Verify: index_of finds item
   - Expected: js_array_index_of(arr, "b") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("index_of finds item")
step("Verify: index_of finds item")
var arr: [text] = ["a", "b", "c"]
expect(js_array_index_of(arr, "b")).to_equal(1)
```

</details>

#### index_of returns -1 for missing

- index_of returns -1 for missing
- Verify: index_of returns -1 for missing
   - Expected: js_array_index_of(arr, "z") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("index_of returns -1 for missing")
step("Verify: index_of returns -1 for missing")
var arr: [text] = ["a", "b"]
expect(js_array_index_of(arr, "z")).to_equal(-1)
```

</details>

#### slice extracts subarray

- slice extracts subarray
- Verify: slice extracts subarray
   - Expected: sliced.len() equals `2`
   - Expected: sliced[0] equals `b`
   - Expected: sliced[1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slice extracts subarray")
step("Verify: slice extracts subarray")
var arr: [text] = ["a", "b", "c", "d"]
val sliced = js_array_slice(arr, 1, 3)
expect(sliced.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(sliced[0]).to_equal("b")
expect(sliced[1]).to_equal("c")
```

</details>

### JS Compat - JSON Stubs

#### json_parse returns input

- json_parse returns input
- Verify: json_parse returns input
   - Expected: js_json_parse("{\"a\":1}") equals `{"a":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("json_parse returns input")
step("Verify: json_parse returns input")
expect(js_json_parse("{\"a\":1}")).to_equal("{\"a\":1}")
```

</details>

#### json_stringify returns input

- json_stringify returns input
- Verify: json_stringify returns input
   - Expected: js_json_stringify("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("json_stringify returns input")
step("Verify: json_stringify returns input")
expect(js_json_stringify("hello")).to_equal("hello")
```

</details>

### JS Compat - URI Encoding

#### encodes space

- encodes space
- Verify: encodes space
   - Expected: result equals `hello%20world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes space")
step("Verify: encodes space")
val result = js_encode_uri_component("hello world")
expect(result).to_equal("hello%20world")
```

</details>

#### encodes special chars

- encodes special chars
- Verify: encodes special chars
   - Expected: result contains `%26`
   - Expected: result contains `%3D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes special chars")
step("Verify: encodes special chars")
val result = js_encode_uri_component("a&b=c")
expect(result.contains("%26")).to_equal(true)
expect(result.contains("%3D")).to_equal(true)
```

</details>

#### does not encode unreserved chars

- does not encode unreserved chars
- Verify: does not encode unreserved chars
   - Expected: result equals `abc-123_test.txt~`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not encode unreserved chars")
step("Verify: does not encode unreserved chars")
val result = js_encode_uri_component("abc-123_test.txt~")
expect(result).to_equal("abc-123_test.txt~")
```

</details>

#### decodes percent-encoded

- decodes percent-encoded
- Verify: decodes percent-encoded
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes percent-encoded")
step("Verify: decodes percent-encoded")
val result = js_decode_uri_component("hello%20world")
expect(result).to_equal("hello world")
```

</details>

#### roundtrips encoding

- roundtrips encoding
- Verify: roundtrips encoding
   - Expected: decoded equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips encoding")
step("Verify: roundtrips encoding")
val original = "hello world!"
val encoded = js_encode_uri_component(original)
val decoded = js_decode_uri_component(encoded)
expect(decoded).to_equal(original)
```

</details>

### JS Compat - Date

#### date_now returns positive timestamp

- date_now returns positive timestamp
- Verify: date_now returns positive timestamp
   - Expected: now > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("date_now returns positive timestamp")
step("Verify: date_now returns positive timestamp")
val now = js_date_now()
expect(now > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BROWSER-SCRIPT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d879cb4f9382c4c895c048a915516df81c63e827bfb5633e501ba2b4abd65887`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d879cb4f9382c4c895c048a915516df81c63e827bfb5633e501ba2b4abd65887`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d879cb4f9382c4c895c048a915516df81c63e827bfb5633e501ba2b4abd65887`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/browser/script/js_compat_spec.spl
mirror: doc/06_spec/unit/browser/script/js_compat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/browser/script/js_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/browser/script/js_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/browser/script/js_compat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/browser/script/js_compat_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses integer from string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser/script/js_compat_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/browser/script/js_compat_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
