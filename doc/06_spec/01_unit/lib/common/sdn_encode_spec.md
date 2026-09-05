# SDN Canonical Encoder Specification

> Tests for `sdn_encode_canonical`: stable canonical output (sorted dict keys, inline collections, minimal quoting with escapes) and the round-trip guarantee `parse(sdn_encode_canonical(v))` reproduces `v`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SDN Canonical Encoder Specification

Tests for `sdn_encode_canonical`: stable canonical output (sorted dict keys, inline collections, minimal quoting with escapes) and the round-trip guarantee `parse(sdn_encode_canonical(v))` reproduces `v`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-SDN |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md (S1) |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/sdn_encode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `sdn_encode_canonical`: stable canonical output (sorted dict keys,
inline collections, minimal quoting with escapes) and the round-trip
guarantee `parse(sdn_encode_canonical(v))` reproduces `v`.

## Scenarios

### sdn_encode_canonical

#### scalars

#### encodes null, bools, and ints

- encodes null, bools, and ints
   - Expected: sdn_encode_canonical(SdnValue.null()) equals `null`
   - Expected: sdn_encode_canonical(SdnValue.bool(true)) equals `true`
   - Expected: sdn_encode_canonical(SdnValue.bool(false)) equals `false`
   - Expected: sdn_encode_canonical(SdnValue.int(-42)) equals `-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes null, bools, and ints")
expect(sdn_encode_canonical(SdnValue.null())).to_equal("null")
expect(sdn_encode_canonical(SdnValue.bool(true))).to_equal("true")
expect(sdn_encode_canonical(SdnValue.bool(false))).to_equal("false")
expect(sdn_encode_canonical(SdnValue.int(-42))).to_equal("-42")
```

</details>

#### keeps a decimal point on floats

- keeps a decimal point on floats
   - Expected: sdn_encode_canonical(SdnValue.float(1.5)) equals `1.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a decimal point on floats")
expect(sdn_encode_canonical(SdnValue.float(1.5))).to_equal("1.5")
```

</details>

#### leaves safe strings bare

- leaves safe strings bare
   - Expected: sdn_encode_canonical(SdnValue.string("hello_world-1/x")) equals `hello_world-1/x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves safe strings bare")
expect(sdn_encode_canonical(SdnValue.string("hello_world-1/x"))).to_equal("hello_world-1/x")
```

</details>

#### quotes strings with spaces

- quotes strings with spaces
   - Expected: sdn_encode_canonical(SdnValue.string("x y")) equals `"x y"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes strings with spaces")
expect(sdn_encode_canonical(SdnValue.string("x y"))).to_equal("\"x y\"")
```

</details>

#### quotes keyword-shaped and number-shaped strings

- quotes keyword-shaped and number-shaped strings
   - Expected: sdn_encode_canonical(SdnValue.string("true")) equals `"true"`
   - Expected: sdn_encode_canonical(SdnValue.string("null")) equals `"null"`
   - Expected: sdn_encode_canonical(SdnValue.string("42")) equals `"42"`
   - Expected: sdn_encode_canonical(SdnValue.string("3.5")) equals `"3.5"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quotes keyword-shaped and number-shaped strings")
expect(sdn_encode_canonical(SdnValue.string("true"))).to_equal("\"true\"")
expect(sdn_encode_canonical(SdnValue.string("null"))).to_equal("\"null\"")
expect(sdn_encode_canonical(SdnValue.string("42"))).to_equal("\"42\"")
expect(sdn_encode_canonical(SdnValue.string("3.5"))).to_equal("\"3.5\"")
```

</details>

#### escapes special characters

- escapes special characters
   - Expected: sdn_encode_canonical(SdnValue.string("a\"b")) equals `"a\\"b"`
   - Expected: sdn_encode_canonical(SdnValue.string("a\\b")) equals `"a\\\\b"`
   - Expected: sdn_encode_canonical(SdnValue.string("a\nb")) equals `"a\\nb"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes special characters")
expect(sdn_encode_canonical(SdnValue.string("a\"b"))).to_equal("\"a\\\"b\"")
expect(sdn_encode_canonical(SdnValue.string("a\\b"))).to_equal("\"a\\\\b\"")
expect(sdn_encode_canonical(SdnValue.string("a\nb"))).to_equal("\"a\\nb\"")
```

</details>

#### collections

#### encodes empty collections

- encodes empty collections
   - Expected: sdn_encode_canonical(SdnValue.empty_array()) equals `[]`
   - Expected: sdn_encode_canonical(SdnValue.empty_dict()) equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty collections")
expect(sdn_encode_canonical(SdnValue.empty_array())).to_equal("[]")
expect(sdn_encode_canonical(SdnValue.empty_dict())).to_equal("{}")
```

</details>

#### encodes arrays inline

- encodes arrays inline
   - Expected: sdn_encode_canonical(v) equals `[1, two, false]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes arrays inline")
val v = SdnValue.array([SdnValue.int(1), SdnValue.string("two"), SdnValue.bool(false)])
expect(sdn_encode_canonical(v)).to_equal("[1, two, false]")
```

</details>

#### sorts dict keys bytewise

- sorts dict keys bytewise
   - Expected: sdn_encode_canonical(SdnValue.Dict(m)) equals `'{a: 1, b: 2, c: 3}'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts dict keys bytewise")
var m: Dict<text, SdnValue> = {}
m["b"] = SdnValue.int(2)
m["a"] = SdnValue.int(1)
m["c"] = SdnValue.int(3)
expect(sdn_encode_canonical(SdnValue.Dict(m))).to_equal('{a: 1, b: 2, c: 3}')
```

</details>

#### encodes nested dicts and arrays inline

- encodes nested dicts and arrays inline
   - Expected: sdn_encode_canonical(SdnValue.Dict(outer)) equals `'{m: {a: "x y", z: [1, 2]}}'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes nested dicts and arrays inline")
var inner: Dict<text, SdnValue> = {}
inner["z"] = SdnValue.array([SdnValue.int(1), SdnValue.int(2)])
inner["a"] = SdnValue.string("x y")
var outer: Dict<text, SdnValue> = {}
outer["m"] = SdnValue.Dict(inner)
expect(sdn_encode_canonical(SdnValue.Dict(outer))).to_equal('{m: {a: "x y", z: [1, 2]}}')
```

</details>

#### round-trip

#### round-trips strings needing escaping

- round-trips strings needing escaping
   - Expected: s equals `original`
   - Expected: "string" equals `reproduced`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips strings needing escaping")
val original = "a\"b\\c\nd\te"
val enc = sdn_encode_canonical(SdnValue.string(original))
match parse(enc):
    case Ok(p):
        match p.as_str():
            case Some(s):
                expect(s).to_equal(original)
            case None:
                expect("string").to_equal("reproduced")
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### round-trips nested arrays and dicts stably

- round-trips nested arrays and dicts stably
   - Expected: sdn_encode_canonical(p) equals `enc`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips nested arrays and dicts stably")
var inner: Dict<text, SdnValue> = {}
inner["k"] = SdnValue.array([SdnValue.int(1), SdnValue.array([SdnValue.string("deep val")])])
var m: Dict<text, SdnValue> = {}
m["b"] = SdnValue.Dict(inner)
m["a"] = SdnValue.float(2.5)
val v = SdnValue.Dict(m)
val enc = sdn_encode_canonical(v)
match parse(enc):
    case Ok(p):
        expect(sdn_encode_canonical(p)).to_equal(enc)
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### round-trips a top-level table

- round-trips a top-level table
   - Expected: enc equals `|name, count|\nalpha, 1\n"two words", 2`
   - Expected: p.is_table() is true
   - Expected: sdn_encode_canonical(p) equals `enc`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a top-level table")
val headers: [text] = ["name", "count"]
val row1: [SdnValue] = [SdnValue.string("alpha"), SdnValue.int(1)]
val row2: [SdnValue] = [SdnValue.string("two words"), SdnValue.int(2)]
val rows: [[SdnValue]] = [row1, row2]
val v = SdnValue.Table(headers, rows)
val enc = sdn_encode_canonical(v)
expect(enc).to_equal("|name, count|\nalpha, 1\n\"two words\", 2")
match parse(enc):
    case Ok(p):
        expect(p.is_table()).to_equal(true)
        expect(sdn_encode_canonical(p)).to_equal(enc)
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

#### round-trips parsed values back to identical canonical text

- round-trips parsed values back to identical canonical text
   - Expected: sdn_encode_canonical(p) equals `enc1`
   - Expected: "parse failed" equals `should not fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips parsed values back to identical canonical text")
val enc1 = '{arr: [1, 2.5, "x y"], flag: true, name: demo}'
match parse(enc1):
    case Ok(p):
        expect(sdn_encode_canonical(p)).to_equal(enc1)
    case Err(_):
        expect("parse failed").to_equal("should not fail")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/app/ide_extension_kernel/parallel_agent_shared_foundation_plan.md (S1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9aead8c52fed8a3bd2cc0aba7f7cb19b793ee6eaa794b3d801ef3431c3848bf4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9aead8c52fed8a3bd2cc0aba7f7cb19b793ee6eaa794b3d801ef3431c3848bf4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9aead8c52fed8a3bd2cc0aba7f7cb19b793ee6eaa794b3d801ef3431c3848bf4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/sdn_encode_spec.spl
mirror: doc/06_spec/01_unit/lib/common/sdn_encode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/sdn_encode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/sdn_encode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/sdn_encode_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes null, bools, and ints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/sdn_encode_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a decimal point on floats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/sdn_encode_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves safe strings bare' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
