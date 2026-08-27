# Volatile Ops Specification

> Tests covering volatile_ops SFFI module, structural sanity, bitand_u32, bitor_u32, mask_invert_u32, read-modify-write pattern, volatile API parameter conventions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Volatile Ops Specification

## Scenarios

### volatile_ops SFFI module

### structural sanity

#### spec file loads without parse error

- spec file loads without parse error
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spec file loads without parse error")
expect(1).to_equal(1)
```

</details>

#### module-level helpers are callable

- module-level helpers are callable
   - Expected: x equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module-level helpers are callable")
val x = test_bitand(0xFF, 0x0F)
expect(x).to_equal(15)
```

</details>

### bitand_u32

#### returns 0 when no bits overlap

- returns 0 when no bits overlap
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 when no bits overlap")
val result = test_bitand(0xF0, 0x0F)
expect(result).to_equal(0)
```

</details>

#### returns common bits for partial overlap

- returns common bits for partial overlap
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns common bits for partial overlap")
val result = test_bitand(0xFF, 0x0F)
expect(result).to_equal(15)
```

</details>

#### returns full value when both operands are equal

- returns full value when both operands are equal
   - Expected: result equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns full value when both operands are equal")
val result = test_bitand(255, 255)
expect(result).to_equal(255)
```

</details>

#### returns 0 when one operand is 0

- returns 0 when one operand is 0
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 when one operand is 0")
val result = test_bitand(0xABCD, 0)
expect(result).to_equal(0)
```

</details>

### bitor_u32

#### combines non-overlapping bits

- combines non-overlapping bits
   - Expected: result equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines non-overlapping bits")
val result = test_bitor(0xF0, 0x0F)
expect(result).to_equal(255)
```

</details>

#### returns same value when one operand is 0

- returns same value when one operand is 0
   - Expected: result equals `171`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same value when one operand is 0")
val result = test_bitor(0xAB, 0)
expect(result).to_equal(171)
```

</details>

#### is idempotent when both operands are equal

- is idempotent when both operands are equal
   - Expected: result equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is idempotent when both operands are equal")
val result = test_bitor(0xFF, 0xFF)
expect(result).to_equal(255)
```

</details>

### mask_invert_u32

#### inverts all bits within 32-bit range

- inverts all bits within 32-bit range
   - Expected: result equals `4294967295`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inverts all bits within 32-bit range")
val result = test_mask_invert(0)
expect(result).to_equal(4294967295)
```

</details>

#### inverts full mask to zero

- inverts full mask to zero
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inverts full mask to zero")
val result = test_mask_invert(4294967295)
expect(result).to_equal(0)
```

</details>

#### inverts partial mask correctly

- inverts partial mask correctly
   - Expected: result equals `4294901760`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inverts partial mask correctly")
# 0x0000FFFF inverted = 0xFFFF0000 = 4294901760
val result = test_mask_invert(65535)
expect(result).to_equal(4294901760)
```

</details>

### read-modify-write pattern

#### clears masked bits and sets new value

- clears masked bits and sets new value
   - Expected: result equals `245`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears masked bits and sets new value")
# initial=0xFF, mask=0x0F (low nibble), value=0x05
# cleared = 0xFF & ~0x0F = 0xFF & 0xF0 = 0xF0 = 240
# updated = 0xF0 | (0x05 & 0x0F) = 0xF0 | 0x05 = 0xF5 = 245
val result = test_rmw(255, 15, 5)
expect(result).to_equal(245)
```

</details>

#### leaves unmasked bits unchanged

- leaves unmasked bits unchanged
   - Expected: result equals `160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves unmasked bits unchanged")
# initial=0xAB=171, mask=0x0F, value=0x00
# clears low nibble: 0xA0=160
val result = test_rmw(171, 15, 0)
expect(result).to_equal(160)
```

</details>

#### sets all masked bits when value equals mask

- sets all masked bits when value equals mask
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets all masked bits when value equals mask")
# initial=0x00, mask=0x0F, value=0x0F → result=0x0F=15
val result = test_rmw(0, 15, 15)
expect(result).to_equal(15)
```

</details>

### volatile API parameter conventions

#### address parameter is i64 (accommodates 64-bit pointers)

- address parameter is i64 (accommodates 64-bit pointers)
   - Expected: combined equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("address parameter is i64 (accommodates 64-bit pointers)")
# Verify the helper accepts i64 addresses without error
val addr: i64 = 0x40020010
val mask: i64 = 0x0001
val combined = test_bitand(addr, mask)
expect(combined).to_equal(0)
```

</details>

#### memory barrier concept: full barrier is distinct from load/store barriers

- memory barrier concept: full barrier is distinct from load/store barriers
   - Expected: full_barrier_id equals `0`
   - Expected: load_barrier_id equals `1`
   - Expected: store_barrier_id equals `2`
   - Expected: full_barrier_id equals `full_barrier_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("memory barrier concept: full barrier is distinct from load/store barriers")
# Conceptual test: three distinct barrier kinds exist
val full_barrier_id: i64 = 0
val load_barrier_id: i64 = 1
val store_barrier_id: i64 = 2
expect(full_barrier_id).to_equal(0)
expect(load_barrier_id).to_equal(1)
expect(store_barrier_id).to_equal(2)
expect(full_barrier_id).to_equal(full_barrier_id)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/volatile_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering volatile_ops SFFI module, structural sanity, bitand_u32, bitor_u32, mask_invert_u32, read-modify-write pattern, volatile API parameter conventions.
- volatile_ops SFFI module
- structural sanity
- bitand_u32
- bitor_u32
- mask_invert_u32
- read-modify-write pattern
- volatile API parameter conventions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `b84eb8be50899320c94db09b0f246a1fbda34da00a46fb1756a46ffe1a7d8ac0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b84eb8be50899320c94db09b0f246a1fbda34da00a46fb1756a46ffe1a7d8ac0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b84eb8be50899320c94db09b0f246a1fbda34da00a46fb1756a46ffe1a7d8ac0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/volatile_ops_spec.spl
mirror: doc/06_spec/unit/app/volatile_ops_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/volatile_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/volatile_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/volatile_ops_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/volatile_ops_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spec file loads without parse error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/volatile_ops_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module-level helpers are callable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/volatile_ops_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 when no bits overlap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
