# Bencode Offset Guard Specification

> Tests covering bencode decode offset guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bencode Offset Guard Specification

## Scenarios

### bencode decode offset guards

#### rejects negative integer decode offsets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative integer decode offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative integer decode offsets")
val r = bencode_decode_int("i42e", -1)
assert_equal(r[0], "error")
```

</details>

#### rejects negative string decode offsets

- rejects negative string decode offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative string decode offsets")
val r = bencode_decode_str("4:spam", -1)
assert_equal(r[0], "error")
```

</details>

#### rejects leading zero string lengths

- rejects leading zero string lengths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects leading zero string lengths")
val r = bencode_decode_str("04:spam", 0)
assert_equal(r[0], "error")
```

</details>

#### rejects oversized integer values before overflow

- rejects oversized integer values before overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized integer values before overflow")
val r = bencode_decode_int("i9223372036854775808e", 0)
assert_equal(r[0], "error")
```

</details>

#### rejects oversized string lengths before overflow

- rejects oversized string lengths before overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized string lengths before overflow")
val r = bencode_decode_str("9223372036854775808:x", 0)
assert_equal(r[0], "error")
```

</details>

#### keeps valid positive offsets

- keeps valid positive offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid positive offsets")
val i = bencode_decode_int("4:spami42e", 6)
assert_equal(i[0], "42")
val s = bencode_decode_str("i42e4:spam", 4)
assert_equal(s[0], "spam")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/bencode_offset_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bencode decode offset guards.
- bencode decode offset guards

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

- Canonical SPipe generation for source `7f3028736172d7832d0d9df3aac2bc569d58b8e26ce86d981c3ef37510cf62ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f3028736172d7832d0d9df3aac2bc569d58b8e26ce86d981c3ef37510cf62ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f3028736172d7832d0d9df3aac2bc569d58b8e26ce86d981c3ef37510cf62ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/bencode_offset_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/bencode_offset_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/bencode_offset_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/bencode_offset_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/bencode_offset_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative integer decode offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/bencode_offset_guard_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative string decode offsets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/bencode_offset_guard_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects leading zero string lengths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
