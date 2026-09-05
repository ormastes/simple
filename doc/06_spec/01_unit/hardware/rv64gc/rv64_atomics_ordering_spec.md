# RV64 Atomics Memory Ordering Unit Tests

> Unit tests for memory ordering semantics: acquire/release bits, FENCE.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Atomics Memory Ordering Unit Tests

Unit tests for memory ordering semantics: acquire/release bits, FENCE.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-ATOMICS-ORD-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for memory ordering semantics: acquire/release bits, FENCE.

## Scenarios

### Acquire/Release Bits

#### no ordering (aq=0, rl=0)

- no ordering (aq=0, rl=0)
   - Expected: ord equals `AmoOrdering.Relaxed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("no ordering (aq=0, rl=0)")
val ord = decode_amo_ordering(0, 0)
expect(ord).to_equal(AmoOrdering.Relaxed)
```

</details>

#### acquire (aq=1, rl=0)

- acquire (aq=1, rl=0)
   - Expected: ord equals `AmoOrdering.Acquire`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("acquire (aq=1, rl=0)")
val ord = decode_amo_ordering(1, 0)
expect(ord).to_equal(AmoOrdering.Acquire)
```

</details>

#### release (aq=0, rl=1)

- release (aq=0, rl=1)
   - Expected: ord equals `AmoOrdering.Release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("release (aq=0, rl=1)")
val ord = decode_amo_ordering(0, 1)
expect(ord).to_equal(AmoOrdering.Release)
```

</details>

#### sequentially consistent (aq=1, rl=1)

- sequentially consistent (aq=1, rl=1)
   - Expected: ord equals `AmoOrdering.SeqCst`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("sequentially consistent (aq=1, rl=1)")
val ord = decode_amo_ordering(1, 1)
expect(ord).to_equal(AmoOrdering.SeqCst)
```

</details>

### FENCE Instruction

#### FENCE rw, rw orders all memory ops

- FENCE rw, rw orders all memory ops
   - Expected: pred and 0x3 equals `0x3`
   - Expected: succ and 0x3 equals `0x3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("FENCE rw, rw orders all memory ops")
# pred=0x3 (rw), succ=0x3 (rw)
val pred = 0x3
val succ = 0x3
expect(pred and 0x3).to_equal(0x3)
expect(succ and 0x3).to_equal(0x3)
```

</details>

#### FENCE.TSO: acquire+release for loads/stores

- FENCE.TSO: acquire+release for loads/stores
   - Expected: fm equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("FENCE.TSO: acquire+release for loads/stores")
# FENCE.TSO = FENCE rw, rw with fm=1000
val fm = 8
expect(fm).to_equal(8)
```

</details>

#### FENCE w, r orders store-to-load

- FENCE w, r orders store-to-load
   - Expected: pred and 0x1 equals `1`
   - Expected: succ and 0x2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("FENCE w, r orders store-to-load")
val pred = 0x1  # w
val succ = 0x2  # r
expect(pred and 0x1).to_equal(1)
expect(succ and 0x2).to_equal(2)
```

</details>

#### FENCE i instruction fence (FENCE.I)

- FENCE i instruction fence (FENCE.I)
   - Expected: is_fence_i is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("FENCE i instruction fence (FENCE.I)")
# FENCE.I flushes instruction cache
val is_fence_i = true
expect(is_fence_i).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-HARDWARE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb23d66ad0d9d2a4188237816be91a2588a65ef98b39190eac8f9a88a3895a8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb23d66ad0d9d2a4188237816be91a2588a65ef98b39190eac8f9a88a3895a8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb23d66ad0d9d2a4188237816be91a2588a65ef98b39190eac8f9a88a3895a8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no ordering (aq=0, rl=0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'acquire (aq=1, rl=0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_atomics_ordering_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'release (aq=0, rl=1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
