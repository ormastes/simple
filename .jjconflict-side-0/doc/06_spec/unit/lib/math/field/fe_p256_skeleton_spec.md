# Fe P256 Skeleton Specification

> Tests covering FeP256 — skeleton constants, FeP256 — skeleton byte round-trip, FeP256 — skeleton equality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fe P256 Skeleton Specification

## Scenarios

### FeP256 — skeleton constants

#### fe_zero encodes to 32 zero bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fe_zero encodes to 32 zero bytes
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_zero encodes to 32 zero bytes")
val out = fe_to_bytes(fe_zero())
var ok = true
var i: u64 = 0
while i < 32:
    if out[i] != 0x00:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### fe_one encodes to 31 zeros followed by 0x01 (big-endian)

- fe_one encodes to 31 zeros followed by 0x01 (big-endian)
   - Expected: ok is true
   - Expected: out[31] equals `0x01`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_one encodes to 31 zeros followed by 0x01 (big-endian)")
val out = fe_to_bytes(fe_one())
var ok = true
var i: u64 = 0
while i < 31:
    if out[i] != 0x00:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
expect(out[31]).to_equal(0x01)
```

</details>

### FeP256 — skeleton byte round-trip

#### Gx round-trips through fe_from_bytes / fe_to_bytes

- Gx round-trips through fe_from_bytes / fe_to_bytes
   - Expected: _bytes_eq(out, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Gx round-trips through fe_from_bytes / fe_to_bytes")
val b = _gx_bytes()
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

#### Gy round-trips through fe_from_bytes / fe_to_bytes

- Gy round-trips through fe_from_bytes / fe_to_bytes
   - Expected: _bytes_eq(out, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Gy round-trips through fe_from_bytes / fe_to_bytes")
val b = _gy_bytes()
val fe = fe_from_bytes(b)
val out = fe_to_bytes(fe)
expect(_bytes_eq(out, b)).to_equal(true)
```

</details>

### FeP256 — skeleton equality

#### fe_eq is reflexive on a decoded point

- fe_eq is reflexive on a decoded point
   - Expected: fe_eq(a, a) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_eq is reflexive on a decoded point")
val a = fe_from_bytes(_gx_bytes())
expect(fe_eq(a, a)).to_equal(true)
```

</details>

#### fe_eq returns false for Gx vs Gy

- fe_eq returns false for Gx vs Gy
   - Expected: fe_eq(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fe_eq returns false for Gx vs Gy")
val a = fe_from_bytes(_gx_bytes())
val b = fe_from_bytes(_gy_bytes())
expect(fe_eq(a, b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/math/field/fe_p256_skeleton_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FeP256 — skeleton constants, FeP256 — skeleton byte round-trip, FeP256 — skeleton equality.
- FeP256 — skeleton constants
- FeP256 — skeleton byte round-trip
- FeP256 — skeleton equality

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b1de8a87785be8edf0cf94f22eedf2eb8ee3c9343d40497335683c8b8845f56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b1de8a87785be8edf0cf94f22eedf2eb8ee3c9343d40497335683c8b8845f56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b1de8a87785be8edf0cf94f22eedf2eb8ee3c9343d40497335683c8b8845f56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/math/field/fe_p256_skeleton_spec.spl
mirror: doc/06_spec/unit/lib/math/field/fe_p256_skeleton_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/math/field/fe_p256_skeleton_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/math/field/fe_p256_skeleton_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/math/field/fe_p256_skeleton_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fe_zero encodes to 32 zero bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/math/field/fe_p256_skeleton_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fe_one encodes to 31 zeros followed by 0x01 (big-endian)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/math/field/fe_p256_skeleton_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Gx round-trips through fe_from_bytes / fe_to_bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
