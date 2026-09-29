# JSON Return Contract Specification

> Purpose: Prove that `json_parse` and the `json_to_*` extractors hand callers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON Return Contract Specification

Purpose: Prove that `json_parse` and the `json_to_*` extractors hand callers

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-JSON-CORE |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Complete |
| Source | `test/01_unit/lib/common/parsers_json_return_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that `json_parse` and the `json_to_*` extractors hand callers
plain values (or nil) instead of tripping the seed's non-optional nil
contract or Option-wrapping the payload.
Audience: stdlib maintainers and anyone parsing JSON with `as i64`/`as f64`.

## Scenarios

### json_parse nil contract

#### returns nil for malformed input instead of trapping

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns nil for malformed input instead of trapping
   - Expected: parsed == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for malformed input instead of trapping")
val parsed = json_parse("{\"a\": ")
expect(parsed == nil).to_equal(true)
```

</details>

#### returns nil for empty input

- returns nil for empty input
   - Expected: json_parse("") == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for empty input")
expect(json_parse("") == nil).to_equal(true)
```

</details>

### json_to_number unwrapped payload

#### compares and casts as a plain number

- compares and casts as a plain number
   - Expected: d < 0.0 is false
   - Expected: i equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compares and casts as a plain number")
val p = json_parse("{\"a\": 150}")
val d = json_to_number(json_object_get(p, "a"))
expect(d < 0.0).to_equal(false)
val i = if d == nil: 0 else: d as i64
expect(i).to_equal(150)
```

</details>

#### float stays float, int stays int

- float stays float, int stays int
   - Expected: f as f64 equals `1.5`
   - Expected: i as i64 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("float stays float, int stays int")
val p = json_parse("{\"f\": 1.5, \"i\": 2}")
val f = json_to_number(json_object_get(p, "f"))
expect(f as f64).to_equal(1.5)
val i = json_to_number(json_object_get(p, "i"))
expect(i as i64).to_equal(2)
```

</details>

#### returns nil for a non-number

- returns nil for a non-number
   - Expected: json_to_number(json_object_get(p, "s")) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for a non-number")
val p = json_parse("{\"s\": \"x\"}")
expect(json_to_number(json_object_get(p, "s")) == nil).to_equal(true)
```

</details>

### json_to_* similar cases

#### string and boolean payloads are plain values

- string and boolean payloads are plain values
   - Expected: json_to_string(json_object_get(p, "s")) equals `advanced-session`
   - Expected: json_to_boolean(json_object_get(p, "b")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("string and boolean payloads are plain values")
val p = json_parse("{\"s\": \"advanced-session\", \"b\": true}")
expect(json_to_string(json_object_get(p, "s"))).to_equal("advanced-session")
expect(json_to_boolean(json_object_get(p, "b"))).to_equal(true)
```

</details>

#### nested null is a null value, not a missing one

- nested null is a null value, not a missing one
   - Expected: json_is_object(outer) is true
   - Expected: inner == nil is false
   - Expected: json_is_null(inner) is true
   - Expected: json_to_number(inner) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("nested null is a null value, not a missing one")
# `}}` inside one literal is lexed as interpolation-close; build via `+`.
val p = json_parse("{\"outer\": {\"inner\": null}" + "}")
val outer = json_object_get(p, "outer")
expect(json_is_object(outer)).to_equal(true)
val inner = json_object_get(outer, "inner")
expect(inner == nil).to_equal(false)
expect(json_is_null(inner)).to_equal(true)
expect(json_to_number(inner) == nil).to_equal(true)
```

</details>

#### numeric-looking key is a string key

- numeric-looking key is a string key
   - Expected: json_to_number(json_object_get(p, "1")) as i64 equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("numeric-looking key is a string key")
val p = json_parse("{\"1\": 10}")
expect(json_to_number(json_object_get(p, "1")) as i64).to_equal(10)
```

</details>

#### empty object and array extract as empty collections

- empty object and array extract as empty collections
   - Expected: json_is_object(o) is true
   - Expected: json_object_size(o) equals `0`
   - Expected: json_is_array(a) is true
   - Expected: json_array_length(a) equals `0`
   - Expected: json_to_array(a).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty object and array extract as empty collections")
val o = json_parse("{}")
expect(json_is_object(o)).to_equal(true)
expect(json_object_size(o)).to_equal(0)
val a = json_parse("[]")
expect(json_is_array(a)).to_equal(true)
expect(json_array_length(a)).to_equal(0)
expect(json_to_array(a).len()).to_equal(0)
```

</details>

#### array element numbers cast directly

- array element numbers cast directly
   - Expected: json_to_number(json_array_get(a, 0)) as i64 equals `3`
   - Expected: json_to_number(json_array_get(a, 1)) as f64 equals `4.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("array element numbers cast directly")
val a = json_parse("[3, 4.5]")
expect(json_to_number(json_array_get(a, 0)) as i64).to_equal(3)
expect(json_to_number(json_array_get(a, 1)) as f64).to_equal(4.5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22a25e09afb6e4db6e6a0a60b6b85023165a2e4e25b920329d61e5ee77f202a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22a25e09afb6e4db6e6a0a60b6b85023165a2e4e25b920329d61e5ee77f202a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22a25e09afb6e4db6e6a0a60b6b85023165a2e4e25b920329d61e5ee77f202a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/parsers_json_return_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/common/parsers_json_return_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/parsers_json_return_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/parsers_json_return_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/parsers_json_return_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/parsers_json_return_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/parsers_json_return_contract_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for malformed input instead of trapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/parsers_json_return_contract_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/parsers_json_return_contract_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares and casts as a plain number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
