# Tls Utilities Slice Byte At Specification

> Tests covering TLS utilities slice/byte_at round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Utilities Slice Byte At Specification

## Scenarios

### TLS utilities slice/byte_at round-trip

#### appends an item instead of dropping it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- appends an item instead of dropping it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends an item instead of dropping it")
val grown: [i64] = append([1, 2], 3)
assert_equal(grown.len(), 3)
assert_equal(byte_at(grown, 2), 3)
```

</details>

#### reports the real collection length

- reports the real collection length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the real collection length")
assert_equal(len(wire_block()), 11)
```

</details>

#### reads bytes out of the source array

- reads bytes out of the source array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads bytes out of the source array")
assert_equal(byte_at(wire_block(), 9), 104)
assert_equal(byte_at(wire_block(), 10), 50)
```

</details>

#### produces a slice of the requested length

- produces a slice of the requested length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a slice of the requested length")
val s: [i64] = slice(wire_block(), 6, 11)
assert_equal(s.len(), 5)
```

</details>

#### reads the sliced bytes back, not zeros

- reads the sliced bytes back, not zeros


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads the sliced bytes back, not zeros")
val s: [i64] = slice(wire_block(), 6, 11)
assert_equal(byte_at(s, 0), 0)
assert_equal(byte_at(s, 1), 3)
assert_equal(byte_at(s, 2), 2)
assert_equal(byte_at(s, 3), 104)
assert_equal(byte_at(s, 4), 50)
```

</details>

#### decodes a big-endian u16 out of a sliced range

- decodes a big-endian u16 out of a sliced range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes a big-endian u16 out of a sliced range")
val s: [i64] = slice(wire_block(), 7, 11)
assert_equal((byte_at(s, 0) * 256) + byte_at(s, 1), 770)
```

</details>

#### clamps an out-of-range end to the source length

- clamps an out-of-range end to the source length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps an out-of-range end to the source length")
val s: [i64] = slice(wire_block(), 9, 99)
assert_equal(s.len(), 2)
assert_equal(byte_at(s, 0), 104)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TLS utilities slice/byte_at round-trip.
- TLS utilities slice/byte_at round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `06c097cc925842c7f86596d99e57a9e8deac490d59fb1b628ef65640c552b6ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06c097cc925842c7f86596d99e57a9e8deac490d59fb1b628ef65640c552b6ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06c097cc925842c7f86596d99e57a9e8deac490d59fb1b628ef65640c552b6ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends an item instead of dropping it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the real collection length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/tls/tls_utilities_slice_byte_at_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads bytes out of the source array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
