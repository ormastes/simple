# JS Compat Spec

> Unit tests for the JS standard library compatibility functions.

<!-- sdn-diagram:id=js_compat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_compat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_compat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_compat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JS Compat Spec

Unit tests for the JS standard library compatibility functions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser/script/js_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the JS standard library compatibility functions.

## Scenarios

### JS Compat - Number Parsing

#### parses integer from string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_parse_int("42")).to_equal(42)
```

</details>

#### parses zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_parse_int("0")).to_equal(0)
```

</details>

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_parse_int("")).to_equal(0)
```

</details>

#### parses float from string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_parse_float("3.14")
expect(result > 3.13).to_equal(true)
expect(result < 3.15).to_equal(true)
```

</details>

#### returns 0.0 for empty float string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_parse_float("")
expect(result == 0.0).to_equal(true)
```

</details>

#### converts to string identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_to_string("hello")).to_equal("hello")
```

</details>

### JS Compat - Number Checks

#### is_finite for normal number

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_is_finite(42.0)).to_equal(true)
```

</details>

#### is_finite for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_is_finite(0.0)).to_equal(true)
```

</details>

### JS Compat - Math

#### floor rounds down

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_math_floor(3.7)).to_equal(3)
```

</details>

#### floor negative rounds down

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_math_floor(-2.3)).to_equal(-3)
```

</details>

#### ceil rounds up

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_math_ceil(3.2)).to_equal(4)
```

</details>

#### round rounds to nearest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_math_round(3.5)).to_equal(4)
```

</details>

#### round rounds down below 0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_math_round(3.4)).to_equal(3)
```

</details>

#### random returns value in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = js_math_random()
expect(r >= 0.0).to_equal(true)
expect(r < 1.0).to_equal(true)
```

</details>

#### abs of positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_math_abs(5.0)
expect(result == 5.0).to_equal(true)
```

</details>

#### abs of negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_math_abs(-5.0)
expect(result == 5.0).to_equal(true)
```

</details>

#### min returns smaller

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_math_min(3.0, 7.0)
expect(result == 3.0).to_equal(true)
```

</details>

#### max returns larger

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_math_max(3.0, 7.0)
expect(result == 7.0).to_equal(true)
```

</details>

#### sqrt of 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_math_sqrt(4.0)
expect(result > 1.99).to_equal(true)
expect(result < 2.01).to_equal(true)
```

</details>

#### sqrt of 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_math_sqrt(0.0)
expect(result == 0.0).to_equal(true)
```

</details>

#### pow integer exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_math_pow(2.0, 10.0)
expect(result == 1024.0).to_equal(true)
```

</details>

#### pow zero exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_math_pow(5.0, 0.0)
expect(result == 1.0).to_equal(true)
```

</details>

#### pi value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pi = js_math_pi()
expect(pi > 3.14).to_equal(true)
expect(pi < 3.15).to_equal(true)
```

</details>

### JS Compat - String

#### splits string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = js_string_split("a,b,c", ",")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("a")
expect(parts[2]).to_equal("c")
```

</details>

#### joins array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = ["x", "y", "z"]
val result = js_string_join(arr, "-")
expect(result).to_equal("x-y-z")
```

</details>

#### trims whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_string_trim("  hi  ")).to_equal("hi")
```

</details>

#### starts_with

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_string_starts_with("hello", "hel")).to_equal(true)
expect(js_string_starts_with("hello", "xyz")).to_equal(false)
```

</details>

#### ends_with

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_string_ends_with("hello", "llo")).to_equal(true)
expect(js_string_ends_with("hello", "xyz")).to_equal(false)
```

</details>

#### includes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_string_includes("hello world", "world")).to_equal(true)
expect(js_string_includes("hello world", "xyz")).to_equal(false)
```

</details>

#### replace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_string_replace("hello world", "world", "there")).to_equal("hello there")
```

</details>

#### to_lower

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_string_to_lower("HELLO")).to_equal("hello")
```

</details>

#### to_upper

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_string_to_upper("hello")).to_equal("HELLO")
```

</details>

### JS Compat - Array

#### push adds item

1. js array push
   - Expected: arr.len() equals `2`
   - Expected: arr[1] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = ["a"]
js_array_push(arr, "b")
expect(arr.len()).to_equal(2)
expect(arr[1]).to_equal("b")
```

</details>

#### pop returns last item

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = ["a", "b", "c"]
val popped = js_array_pop(arr)
expect(popped).to_equal("c")
expect(arr.len()).to_equal(2)
```

</details>

#### pop empty returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = []
val popped = js_array_pop(arr)
expect(popped).to_equal("")
```

</details>

#### length returns count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = ["a", "b"]
expect(js_array_length(arr)).to_equal(2)
```

</details>

#### index_of finds item

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = ["a", "b", "c"]
expect(js_array_index_of(arr, "b")).to_equal(1)
```

</details>

#### index_of returns -1 for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = ["a", "b"]
expect(js_array_index_of(arr, "z")).to_equal(-1)
```

</details>

#### slice extracts subarray

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [text] = ["a", "b", "c", "d"]
val sliced = js_array_slice(arr, 1, 3)
expect(sliced.len()).to_equal(2)
expect(sliced[0]).to_equal("b")
expect(sliced[1]).to_equal("c")
```

</details>

### JS Compat - JSON Stubs

#### json_parse returns input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_json_parse("{\"a\":1}")).to_equal("{\"a\":1}")
```

</details>

#### json_stringify returns input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_json_stringify("hello")).to_equal("hello")
```

</details>

### JS Compat - URI Encoding

#### encodes space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_encode_uri_component("hello world")
expect(result).to_equal("hello%20world")
```

</details>

#### encodes special chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_encode_uri_component("a&b=c")
expect(result.contains("%26")).to_equal(true)
expect(result.contains("%3D")).to_equal(true)
```

</details>

#### does not encode unreserved chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_encode_uri_component("abc-123_test.txt~")
expect(result).to_equal("abc-123_test.txt~")
```

</details>

#### decodes percent-encoded

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = js_decode_uri_component("hello%20world")
expect(result).to_equal("hello world")
```

</details>

#### roundtrips encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "hello world!"
val encoded = js_encode_uri_component(original)
val decoded = js_decode_uri_component(encoded)
expect(decoded).to_equal(original)
```

</details>

### JS Compat - Date

#### date_now returns positive timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
