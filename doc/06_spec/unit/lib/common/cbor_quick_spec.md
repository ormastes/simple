# Cbor Quick Specification

> Tests covering quick test.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Quick Specification

## Scenarios

### quick test

#### text_to_bytes single char

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- text_to_bytes single char
   - Expected: result.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text_to_bytes single char")
val result = text_to_bytes("a")
expect(result.len()).to_equal(1)
```

</details>

#### text_to_bytes multi char

- text_to_bytes multi char
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text_to_bytes multi char")
val result = text_to_bytes("ab")
expect(result.len()).to_equal(2)
```

</details>

#### var name test my_bytes

- var name test my_bytes
   - Expected: cbor_validate(my_bytes) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("var name test my_bytes")
val my_bytes: [i64] = []
expect(cbor_validate(my_bytes)).to_equal(false)
```

</details>

#### var name test bytes

- var name test bytes
   - Expected: cbor_validate(bytes) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("var name test bytes")
val bytes: [i64] = []
expect(cbor_validate(bytes)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/cbor_quick_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering quick test.
- quick test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a89b2a93b055a2c69dd28729f4e98133268a93ea523e534d1c40ad16f39975bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a89b2a93b055a2c69dd28729f4e98133268a93ea523e534d1c40ad16f39975bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a89b2a93b055a2c69dd28729f4e98133268a93ea523e534d1c40ad16f39975bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/cbor_quick_spec.spl
mirror: doc/06_spec/unit/lib/common/cbor_quick_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/cbor_quick_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/cbor_quick_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/cbor_quick_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/cbor_quick_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'text_to_bytes single char' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/cbor_quick_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'text_to_bytes multi char' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/cbor_quick_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'var name test my_bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
