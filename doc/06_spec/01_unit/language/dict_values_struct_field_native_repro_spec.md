# Dict Values Struct Field Native Repro Specification

> Tests covering Dict.values() / .keys() loop element field reads.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Values Struct Field Native Repro Specification

## Scenarios

### Dict.values() / .keys() loop element field reads

#### reads every field of a struct value, not just field 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads every field of a struct value, not just field 0
   - Expected: seen_a equals `7`
   - Expected: seen_b equals `hi`
   - Expected: seen_c equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("reads every field of a struct value, not just field 0")
var d: Dict<i64, DvPoint> = {}
d[1] = DvPoint(a: 7, b: "hi", c: 11)
var seen_a = 0
var seen_b = ""
var seen_c = 0
for p in d.values():
    seen_a = p.a
    seen_b = p.b
    seen_c = p.c
expect(seen_a).to_equal(7)
expect(seen_b).to_equal("hi")
expect(seen_c).to_equal(11)
```

</details>

#### reads every field when .values() is hoisted into a local first

- reads every field when .values() is hoisted into a local first
   - Expected: seen_b equals `hoisted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("reads every field when .values() is hoisted into a local first")
var d: Dict<i64, DvPoint> = {}
d[2] = DvPoint(a: 1, b: "hoisted", c: 3)
val vs = d.values()
var seen_b = ""
for p in vs:
    seen_b = p.b
expect(seen_b).to_equal("hoisted")
```

</details>

#### reads every field for a dict with text keys and struct values

- reads every field for a dict with text keys and struct values
   - Expected: seen_b equals `zz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("reads every field for a dict with text keys and struct values")
var d: Dict<text, DvPoint> = {}
d["z"] = DvPoint(a: 1, b: "zz", c: 2)
var seen_b = ""
for p in d.values():
    seen_b = p.b
expect(seen_b).to_equal("zz")
```

</details>

#### keeps text keys intact through .keys()

- keeps text keys intact through .keys()
   - Expected: seen equals `kx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("keeps text keys intact through .keys()")
var d: Dict<text, i64> = {}
d["kx"] = 5
var seen = ""
for k in d.keys():
    seen = k
expect(seen).to_equal("kx")
```

</details>

#### control: d[k] direct read was never affected

- control: d[k] direct read was never affected
   - Expected: d[1].b equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("control: d[k] direct read was never affected")
var d: Dict<i64, DvPoint> = {}
d[1] = DvPoint(a: 7, b: "hi", c: 11)
expect(d[1].b).to_equal("hi")
```

</details>

#### control: array-literal iteration was never affected

- control: array-literal iteration was never affected
   - Expected: seen_b equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("control: array-literal iteration was never affected")
val arr: [DvPoint] = [DvPoint(a: 7, b: "hi", c: 11)]
var seen_b = ""
for q in arr:
    seen_b = q.b
expect(seen_b).to_equal("hi")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/dict_values_struct_field_native_repro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Dict.values() / .keys() loop element field reads.
- Dict.values() / .keys() loop element field reads

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed06866dacff7040b0dd6d7cdf7185a082b6f98caecfeb8d1287dd9a667fed7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed06866dacff7040b0dd6d7cdf7185a082b6f98caecfeb8d1287dd9a667fed7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed06866dacff7040b0dd6d7cdf7185a082b6f98caecfeb8d1287dd9a667fed7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/language/dict_values_struct_field_native_repro_spec.spl
mirror: doc/06_spec/01_unit/language/dict_values_struct_field_native_repro_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/dict_values_struct_field_native_repro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/dict_values_struct_field_native_repro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/dict_values_struct_field_native_repro_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/dict_values_struct_field_native_repro_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads every field of a struct value, not just field 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/dict_values_struct_field_native_repro_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads every field when .values() is hoisted into a local first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/dict_values_struct_field_native_repro_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads every field for a dict with text keys and struct values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
