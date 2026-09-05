# Utf16 Decode Unit Guard Specification

> Tests covering utf16 decode unit guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Utf16 Decode Unit Guard Specification

## Scenarios

### utf16 decode unit guards

#### keeps valid unit decode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid unit decode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid unit decode")
assert_equal(utf16_decode_one([0x41], 0), [0x41, 1])
```

</details>

#### rejects negative code units

- rejects negative code units


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative code units")
assert_equal(utf16_decode_one([-1], 0), [0xFFFD, 1])
```

</details>

#### rejects code units above 16 bits

- rejects code units above 16 bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects code units above 16 bits")
assert_equal(utf16_decode_one([0x10041], 0), [0xFFFD, 1])
```

</details>

#### rejects malformed low surrogate units

- rejects malformed low surrogate units


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed low surrogate units")
assert_equal(utf16_decode_one([0xD83D, 0x1DE00], 0), [0xFFFD, 1])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/utf16_decode_unit_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering utf16 decode unit guards.
- utf16 decode unit guards

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

- Canonical SPipe generation for source `43db4aa8fb7ce9cc5a1f0ce51f2ceff806ca2d2299e706973043035b78e5fd51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43db4aa8fb7ce9cc5a1f0ce51f2ceff806ca2d2299e706973043035b78e5fd51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43db4aa8fb7ce9cc5a1f0ce51f2ceff806ca2d2299e706973043035b78e5fd51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/utf16_decode_unit_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/utf16_decode_unit_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/utf16_decode_unit_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/utf16_decode_unit_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/utf16_decode_unit_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid unit decode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/utf16_decode_unit_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative code units' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/utf16_decode_unit_guard_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects code units above 16 bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
