# json_logic_spec

> Purpose: Prove that JSON Library Logic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# json_logic_spec

Purpose: Prove that JSON Library Logic.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/json_logic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that JSON Library Logic.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### JSON Library Logic

### parser strictness

#### parses nested object and array values

- parses nested object and array values
- Verify: parses nested object and array values
   - Expected: json_is_object(parsed) is true
   - Expected: json_to_string(json_path_get(parsed, "user.name")) equals `Ada`
   - Expected: json_to_number(json_path_get(parsed, "user.scores.1")) equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses nested object and array values")
step("Verify: parses nested object and array values")
# @req: REQ-LIB-COMMON-001
val parsed = json_parse("{\"user\":{\"name\":\"Ada\",\"scores\":[1,2]}}}")
expect(json_is_object(parsed)).to_equal(true)
expect(json_to_string(json_path_get(parsed, "user.name"))).to_equal("Ada")
expect(json_to_number(json_path_get(parsed, "user.scores.1"))).to_equal(2.0)
```

</details>

#### rejects trailing tokens after a valid value

- rejects trailing tokens after a valid value
- Verify: rejects trailing tokens after a valid value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects trailing tokens after a valid value")
step("Verify: rejects trailing tokens after a valid value")
val parsed = json_parse("{\"ok\":true} []")
expect(parsed).to_be_nil()

val result = json_parse_with_error("{\"ok\":true} []")
expect(result.0).to_be_nil()
expect(result.1).to_contain("trailing")
```

</details>

#### rejects trailing commas in objects

- rejects trailing commas in objects
- Verify: rejects trailing commas in objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects trailing commas in objects")
step("Verify: rejects trailing commas in objects")
val parsed = json_parse("{\"ok\":true,}")
expect(parsed).to_be_nil()

val result = json_parse_with_error("{\"ok\":true,}")
expect(result.0).to_be_nil()
expect(result.1).to_contain("Trailing comma")
```

</details>

#### rejects trailing commas in arrays

- rejects trailing commas in arrays
- Verify: rejects trailing commas in arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects trailing commas in arrays")
step("Verify: rejects trailing commas in arrays")
val parsed = json_parse("[1,2,]")
expect(parsed).to_be_nil()

val result = json_parse_with_error("[1,2,]")
expect(result.0).to_be_nil()
expect(result.1).to_contain("Unexpected token")
```

</details>

#### reports unterminated strings

- reports unterminated strings
- Verify: reports unterminated strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports unterminated strings")
step("Verify: reports unterminated strings")
val result = json_parse_with_error("{\"name\":\"Ada}")
expect(result.0).to_be_nil()
expect(result.1).to_contain("Unterminated string")
```

</details>

#### decodes escaped slash and control escapes in strings

- decodes escaped slash and control escapes in strings
- Verify: decodes escaped slash and control escapes in strings
   - Expected: json_to_string(json_path_get(parsed, "path")) equals `https://example.com\b\f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes escaped slash and control escapes in strings")
step("Verify: decodes escaped slash and control escapes in strings")
val parsed = json_parse("{\"path\":\"https:\\/\\/example.com\\b\\f\"}")
expect(json_to_string(json_path_get(parsed, "path"))).to_equal("https://example.com\b\f")
```

</details>

#### rejects unknown string escapes

- rejects unknown string escapes
- Verify: rejects unknown string escapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unknown string escapes")
step("Verify: rejects unknown string escapes")
val result = json_parse_with_error("{\"path\":\"\\q\"}")
expect(result.0).to_be_nil()
expect(result.1).to_contain("Invalid string escape")
```

</details>

#### rejects raw control characters in strings

- rejects raw control characters in strings
- Verify: rejects raw control characters in strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects raw control characters in strings")
step("Verify: rejects raw control characters in strings")
val input = "{" + "\"path\":\"ok" + text.from_char_code(1) + "\"" + "}"
val result = json_parse_with_error(input)
expect(result.0).to_be_nil()
expect(result.1).to_contain("Invalid string escape")
```

</details>

#### rejects truncated and malformed unicode escapes

- rejects truncated and malformed unicode escapes
- Verify: rejects truncated and malformed unicode escapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects truncated and malformed unicode escapes")
step("Verify: rejects truncated and malformed unicode escapes")
val truncated = json_parse_with_error("{\"path\":\"\\u12\"}")
val bad_hex = json_parse_with_error("{\"path\":\"\\u12xz\"}")
expect(truncated.0).to_be_nil()
expect(bad_hex.0).to_be_nil()
```

</details>

#### accepts complete unicode escapes

- accepts complete unicode escapes
- Verify: accepts complete unicode escapes
   - Expected: result.1 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts complete unicode escapes")
step("Verify: accepts complete unicode escapes")
val result = json_parse_with_error("{\"path\":\"\\u12AF\"}")
expect(result.1).to_equal("")
```

</details>

#### rejects malformed number token mixes

- rejects malformed number token mixes
- Verify: rejects malformed number token mixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed number token mixes")
step("Verify: rejects malformed number token mixes")
val result = json_parse_with_error("{\"value\":1e+}")
expect(result.0).to_be_nil()
expect(result.1).to_contain("Invalid number")
```

</details>

#### rejects incomplete and non-canonical numbers

- rejects incomplete and non-canonical numbers
- Verify: rejects incomplete and non-canonical numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects incomplete and non-canonical numbers")
step("Verify: rejects incomplete and non-canonical numbers")
val bare_minus = json_parse_with_error("-")
val leading_zero = json_parse_with_error("01")
val incomplete_fraction = json_parse_with_error("1.")
val incomplete_exponent = json_parse_with_error("1e")
expect(bare_minus.0).to_be_nil()
expect(leading_zero.0).to_be_nil()
expect(incomplete_fraction.0).to_be_nil()
expect(incomplete_exponent.0).to_be_nil()
```

</details>

#### accepts valid negative decimal and exponent numbers

- accepts valid negative decimal and exponent numbers
- Verify: accepts valid negative decimal and exponent numbers
   - Expected: json_parse_with_error("-0").1 equals ``
   - Expected: json_parse_with_error("-0.25").1 equals ``
   - Expected: json_parse_with_error("1.25e-2").1 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts valid negative decimal and exponent numbers")
step("Verify: accepts valid negative decimal and exponent numbers")
expect(json_parse_with_error("-0").1).to_equal("")
expect(json_parse_with_error("-0.25").1).to_equal("")
expect(json_parse_with_error("1.25e-2").1).to_equal("")
```

</details>

#### rejects trailing characters after a number

- rejects trailing characters after a number
- Verify: rejects trailing characters after a number


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects trailing characters after a number")
step("Verify: rejects trailing characters after a number")
val result = json_parse_with_error("1x")
expect(result.0).to_be_nil()
expect(result.1).to_contain("trailing")
```

</details>

#### validates every nonempty JSONL record

- validates every nonempty JSONL record
- Verify: validates every nonempty JSONL record
   - Expected: jsonl_is_valid("{\"ok\":true}\n[1,2]\n") is true
   - Expected: jsonl_is_valid("{\"ok\":true}\n{\"truncated\":") is false
   - Expected: jsonl_is_valid("{\"ok\":true}\n\n[1,2]") is false
   - Expected: jsonl_is_valid("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates every nonempty JSONL record")
step("Verify: validates every nonempty JSONL record")
expect(jsonl_is_valid("{\"ok\":true}\n[1,2]\n")).to_equal(true)
expect(jsonl_is_valid("{\"ok\":true}\n{\"truncated\":")).to_equal(false)
expect(jsonl_is_valid("{\"ok\":true}\n\n[1,2]")).to_equal(false)
expect(jsonl_is_valid("")).to_equal(false)
```

</details>

#### rejects JSONL control-only records and unreadable content

- rejects JSONL control-only records and unreadable content
- Verify: rejects JSONL control-only records and unreadable content
   - Expected: jsonl_is_valid(text.from_char_code(11)) is false
   - Expected: jsonl_is_valid(text.from_char_code(12)) is false
   - Expected: jsonl_content_is_valid(nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects JSONL control-only records and unreadable content")
step("Verify: rejects JSONL control-only records and unreadable content")
expect(jsonl_is_valid(text.from_char_code(11))).to_equal(false)
expect(jsonl_is_valid(text.from_char_code(12))).to_equal(false)
expect(jsonl_content_is_valid(nil)).to_equal(false)
```

</details>

#### keeps invalid trailing input unchanged during minify and beautify

- keeps invalid trailing input unchanged during minify and beautify
- Verify: keeps invalid trailing input unchanged during minify and beautify
   - Expected: json_minify(input) equals `input`
   - Expected: json_beautify(input) equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps invalid trailing input unchanged during minify and beautify")
step("Verify: keeps invalid trailing input unchanged during minify and beautify")
val input = "{\"ok\":true} garbage"
expect(json_minify(input)).to_equal(input)
expect(json_beautify(input)).to_equal(input)
```

</details>

### path write semantics

#### creates missing nested objects for dotted paths

- creates missing nested objects for dotted paths
- Verify: creates missing nested objects for dotted paths
   - Expected: json_is_object(json_object_get(updated, "user")) is true
   - Expected: json_to_string(json_path_get(updated, "user.profile.name")) equals `Ada`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates missing nested objects for dotted paths")
step("Verify: creates missing nested objects for dotted paths")
val updated = json_path_set(json_object({}), "user.profile.name", json_string("Ada"))
expect(json_is_object(json_object_get(updated, "user"))).to_equal(true)
expect(json_to_string(json_path_get(updated, "user.profile.name"))).to_equal("Ada")
```

</details>

#### preserves existing siblings when writing nested paths

- preserves existing siblings when writing nested paths
- Verify: preserves existing siblings when writing nested paths
   - Expected: json_to_number(json_path_get(updated, "user.id")) equals `7`
   - Expected: json_to_string(json_path_get(updated, "user.profile.name")) equals `Ada`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves existing siblings when writing nested paths")
step("Verify: preserves existing siblings when writing nested paths")
val original = json_object({
    "user": json_object({
        "id": json_number(7)
    })
})
val updated = json_path_set(original, "user.profile.name", json_string("Ada"))
expect(json_to_number(json_path_get(updated, "user.id"))).to_equal(7)
expect(json_to_string(json_path_get(updated, "user.profile.name"))).to_equal("Ada")
```

</details>

### unflatten behavior

#### builds nested objects from dotted keys

- builds nested objects from dotted keys
- Verify: builds nested objects from dotted keys
   - Expected: json_to_string(json_path_get(nested, "user.name")) equals `Ada`
   - Expected: json_to_number(json_path_get(nested, "user.age")) equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds nested objects from dotted keys")
step("Verify: builds nested objects from dotted keys")
val flat = json_object({
    "user.name": json_string("Ada"),
    "user.age": json_number(37)
})
val nested = json_unflatten_object(flat)
expect(json_to_string(json_path_get(nested, "user.name"))).to_equal("Ada")
expect(json_to_number(json_path_get(nested, "user.age"))).to_equal(37)
```

</details>

### diff and patch behavior

#### applies object diffs back to the original object

- applies object diffs back to the original object
- Verify: applies object diffs back to the original object
   - Expected: json_deep_equals(patched, updated) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies object diffs back to the original object")
step("Verify: applies object diffs back to the original object")
val original = json_object({
    "user": json_object({
        "name": json_string("Ada"),
        "age": json_number(36)
    }),
    "tags": json_array([json_string("core")])
})
val updated = json_object({
    "user": json_object({
        "name": json_string("Ada"),
        "age": json_number(37)
    }),
    "tags": json_array([json_string("core")]),
    "active": json_string("yes")
})

val diff = json_diff(original, updated)
val patched = json_patch(original, diff)

expect(json_deep_equals(patched, updated)).to_equal(true)
```

</details>

### builder escaping

#### escapes object keys as well as values

- escapes object keys as well as values
- Verify: escapes object keys as well as values
   - Expected: built equals `{"say\\"hi": "line\\nbreak"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes object keys as well as values")
step("Verify: escapes object keys as well as values")
val built = JsonBuilder.object()
    .field("say\"hi", "line\nbreak")
    .build()

expect(built).to_equal("{\"say\\\"hi\": \"line\\nbreak\"}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `684d116331bb9195daf977ee208788709ee0c4d7df5d60290b2046302296af61`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `684d116331bb9195daf977ee208788709ee0c4d7df5d60290b2046302296af61`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `684d116331bb9195daf977ee208788709ee0c4d7df5d60290b2046302296af61`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/json_logic_spec.spl
mirror: doc/06_spec/01_unit/lib/common/json_logic_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/json_logic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/json_logic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/json_logic_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/json_logic_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses nested object and array values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/json_logic_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects trailing tokens after a valid value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/json_logic_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects trailing commas in objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
