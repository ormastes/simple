# Ctypes Hex Guard Specification

> Tests covering typed crypto hex guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ctypes Hex Guard Specification

## Scenarios

### typed crypto hex guards

#### keeps valid digest hex decoding

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid digest hex decoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid digest hex decoding")
val d = Digest.from_hex("deadbeef")
assert_equal(d.len(), 4)
assert_equal(d.hex(), "deadbeef")
```

</details>

#### rejects odd-length digest hex

- rejects odd-length digest hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects odd-length digest hex")
val d = Digest.from_hex("abc")
assert_equal(d.len(), 0)
```

</details>

#### rejects invalid digest hex characters

- rejects invalid digest hex characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid digest hex characters")
val d = Digest.from_hex("dezg")
assert_equal(d.len(), 0)
```

</details>

#### rejects malformed MAC tag hex

- rejects malformed MAC tag hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed MAC tag hex")
val m = MacTag.from_hex("ca?e")
assert_equal(m.len(), 0)
```

</details>

#### rejects malformed secret key hex

- rejects malformed secret key hex


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed secret key hex")
val k = SecretKey.from_hex("00xz")
assert_equal(k.len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/typed/ctypes_hex_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering typed crypto hex guards.
- typed crypto hex guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `f13d9b793af6d6da549d90500e389f97193977905f723445a4f8cffe195bdaa1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f13d9b793af6d6da549d90500e389f97193977905f723445a4f8cffe195bdaa1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f13d9b793af6d6da549d90500e389f97193977905f723445a4f8cffe195bdaa1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/crypto/typed/ctypes_hex_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/typed/ctypes_hex_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/crypto/typed/ctypes_hex_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/typed/ctypes_hex_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/typed/ctypes_hex_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid digest hex decoding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/typed/ctypes_hex_guard_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects odd-length digest hex' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/typed/ctypes_hex_guard_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid digest hex characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
