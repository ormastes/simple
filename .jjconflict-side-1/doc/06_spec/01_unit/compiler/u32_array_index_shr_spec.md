# U32 Array Index Shr Specification

> Tests covering Indexed `[u32]` read narrows before `>>` (A2 / FR-DRIVER-0002b array variant).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U32 Array Index Shr Specification

## Scenarios

### Indexed `[u32]` read narrows before `>>` (A2 / FR-DRIVER-0002b array variant)

#### AC-1a: arr[0] >> 3 with arr[0]=0x80000000 yields 0x10000000 (unsigned logical shift)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-1a: arr[0] >> 3 with arr[0]=0x80000000 yields 0x10000000 (unsigned logical shift)
   - Expected: got equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-1a: arr[0] >> 3 with arr[0]=0x80000000 yields 0x10000000 (unsigned logical shift)")
val got: u32 = u32_array_high_bit_shr3()
val expected: u32 = 0x10000000 as u32
expect(got).to_equal(expected)
```

</details>

#### AC-1b: arr[0] >> 3 with arr[0]=0xFFFFFFFF yields 0x1FFFFFFF (unsigned logical shift)

- AC-1b: arr[0] >> 3 with arr[0]=0xFFFFFFFF yields 0x1FFFFFFF (unsigned logical shift)
   - Expected: got equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-1b: arr[0] >> 3 with arr[0]=0xFFFFFFFF yields 0x1FFFFFFF (unsigned logical shift)")
val got: u32 = u32_array_all_ones_shr3()
val expected: u32 = 0x1FFFFFFF as u32
expect(got).to_equal(expected)
```

</details>

#### AC-1b2: dynamic [u32; count] repeat preserves all 32 bits

- AC-1b2: dynamic [u32; count] repeat preserves all 32 bits
   - Expected: u32_array_dynamic_repeat(3) equals `0xFFFFFFFF as u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-1b2: dynamic [u32; count] repeat preserves all 32 bits")
expect(u32_array_dynamic_repeat(3)).to_equal(0xFFFFFFFF as u32)
```

</details>

#### AC-1c: SHA-recurrence shape `arr[a] + ((arr[b] >> 3) ^ arr[c])` yields unsigned-correct 0x210F0F0F

- AC-1c: SHA-recurrence shape `arr[a] + ((arr[b] >> 3) ^ arr[c])` yields unsigned-correct 0x210F0F0F
   - Expected: got equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-1c: SHA-recurrence shape `arr[a] + ((arr[b] >> 3) ^ arr[c])` yields unsigned-correct 0x210F0F0F")
# Mirrors `w[t-16] + small_sigma0-like(w[t-15]) + ... ^ ...` from
# src/os/crypto/sha256.spl:220-280 at minimum scale.  Distinguishes
# signed-i64 lowering (wrong: 0x010F0F0F) from u32-narrowed (right).
val got: u32 = u32_sha_recurrence_shape()
val expected: u32 = 0x210F0F0F as u32
expect(got).to_equal(expected)
```

</details>

<details>
<summary>Advanced: AC-1d: for-loop `for w in arr: acc += w >> 3` matches direct indexed read</summary>

#### AC-1d: for-loop `for w in arr: acc += w >> 3` matches direct indexed read

- AC-1d: for-loop `for w in arr: acc += w >> 3` matches direct indexed read
   - Expected: got equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-1d: for-loop `for w in arr: acc += w >> 3` matches direct indexed read")
val got: u32 = u32_array_for_loop_shr3()
val expected: u32 = 0x10000000 as u32
expect(got).to_equal(expected)
```

</details>


</details>

#### AC-1e: signed [i32] arr[0] >> 3 still arithmetic-shifts (-1 >> 3 == -1)

- AC-1e: signed [i32] arr[0] >> 3 still arithmetic-shifts (-1 >> 3 == -1)
   - Expected: i32_array_minus_one_shr3() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-1e: signed [i32] arr[0] >> 3 still arithmetic-shifts (-1 >> 3 == -1)")
# Guard against an over-eager fix that drops signedness for [i32] too.
# SIGNED narrow path must keep `signed: true` in UnitNarrow so the
# downstream `>>` dispatches to `sshr`.
expect(i32_array_minus_one_shr3()).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u32_array_index_shr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Indexed `[u32]` read narrows before `>>` (A2 / FR-DRIVER-0002b array variant).
- Indexed `[u32]` read narrows before `>>` (A2 / FR-DRIVER-0002b array variant)

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c2285f3344051ddfe14ab00c9591fcfff74d8ca9bddaf0f441c085194ff7fb1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c2285f3344051ddfe14ab00c9591fcfff74d8ca9bddaf0f441c085194ff7fb1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c2285f3344051ddfe14ab00c9591fcfff74d8ca9bddaf0f441c085194ff7fb1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/u32_array_index_shr_spec.spl
mirror: doc/06_spec/01_unit/compiler/u32_array_index_shr_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/u32_array_index_shr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/u32_array_index_shr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/u32_array_index_shr_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/u32_array_index_shr_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1a: arr[0] >> 3 with arr[0]=0x80000000 yields 0x10000000 (unsigned logical shift)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u32_array_index_shr_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1b: arr[0] >> 3 with arr[0]=0xFFFFFFFF yields 0x1FFFFFFF (unsigned logical shift)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u32_array_index_shr_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1b2: dynamic [u32; count] repeat preserves all 32 bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
