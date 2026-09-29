# Mission Ready Set Specification

> Tests covering mission scalar ready set.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mission Ready Set Specification

## Scenarios

### mission scalar ready set

#### rejects invalid owners and capacities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects invalid owners and capacities


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid owners and capacities")
expect(MissionReadySet64.create(0u64, 1u64)).to_equal(
    Err(MissionReadySetError.InvalidOwner))
expect(MissionReadySet64.create(1u64, 0u64)).to_equal(
    Err(MissionReadySetError.InvalidCapacity))
expect(MissionReadySet64.create(1u64, 65u64)).to_equal(
    Err(MissionReadySetError.InvalidCapacity))
```

</details>

#### seals once and reports only evidence the source can support

- seals once and reports only evidence the source can support
   - Expected: set.phase() equals `MissionReadySetPhase.Configuring`
   - Expected: set.seal(9u64) equals `Err(MissionReadySetError.WrongOwner)`
   - Expected: set.seal(41u64) equals `Err(MissionReadySetError.AlreadyReady)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seals once and reports only evidence the source can support")
var set = match MissionReadySet64.create(41u64, 64u64):
    case Ok(value): value
    case Err(_): panic("create failed")
expect(set.phase()).to_equal(MissionReadySetPhase.Configuring)
expect(set.seal(9u64)).to_equal(Err(MissionReadySetError.WrongOwner))
val receipt = match set.seal(41u64):
    case Ok(value): value
    case Err(_): panic("seal failed")
expect(receipt.inline_scalar_shape).to_be(true)
expect(receipt.source_has_no_explicit_allocation).to_be(true)
expect(receipt.compiler_placement_proven).to_be(false)
expect(receipt.link_time_static_proven).to_be(false)
expect(receipt.backend_allocation_free_proven).to_be(false)
expect(set.seal(41u64)).to_equal(Err(MissionReadySetError.AlreadyReady))
```

</details>

#### admits and wakes one exact slot without scanning

- admits and wakes one exact slot without scanning
   - Expected: set.post_ready(41u64, token) equals `Ok(())`
   - Expected: set.claim_ready(41u64, token) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits and wakes one exact slot without scanning")
var set = ready_set(8u64)
val token = match set.admit(41u64, 5u64):
    case Ok(value): value
    case Err(_): panic("admit failed")
expect(set.is_occupied(5u64)).to_be(true)
expect(set.is_ready(5u64)).to_be(false)
expect(set.post_ready(41u64, token)).to_equal(Ok(()))
expect(set.is_ready(5u64)).to_be(true)
expect(set.claim_ready(41u64, token)).to_equal(Ok(()))
expect(set.is_ready(5u64)).to_be(false)
expect(set.claim_ready(41u64, token)).to_equal(
    Err(MissionReadySetError.NotPosted))
```

</details>

#### rejects duplicate, vacant, out-of-range, and wrong-owner operations

- rejects duplicate, vacant, out-of-range, and wrong-owner operations
   - Expected: set.release(41u64, token) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate, vacant, out-of-range, and wrong-owner operations")
var set = ready_set(2u64)
val token = match set.admit(41u64, 1u64):
    case Ok(value): value
    case Err(_): panic("admit failed")
expect(set.admit(41u64, 1u64)).to_equal(
    Err(MissionReadySetError.SlotOccupied))
expect(set.admit(41u64, 2u64)).to_equal(
    Err(MissionReadySetError.InvalidSlot))
expect(set.post_ready(9u64, token)).to_equal(
    Err(MissionReadySetError.WrongOwner))
expect(set.release(41u64, token)).to_equal(Ok(()))
expect(set.post_ready(41u64, token)).to_equal(
    Err(MissionReadySetError.SlotVacant))
```

</details>

#### invalidates all pre-reset tokens by generation

- invalidates all pre-reset tokens by generation
   - Expected: reset_receipt.generation equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates all pre-reset tokens by generation")
var set = ready_set(4u64)
val old_token = match set.admit(41u64, 2u64):
    case Ok(value): value
    case Err(_): panic("admit failed")
val reset_receipt = match set.reset(41u64):
    case Ok(value): value
    case Err(_): panic("reset failed")
expect(reset_receipt.generation).to_equal(2u64)
expect(set.post_ready(41u64, old_token)).to_equal(
    Err(MissionReadySetError.StaleGeneration))
expect(set.is_occupied(2u64)).to_be(false)
```

</details>

#### quiesces terminally and rejects subsequent operations

- quiesces terminally and rejects subsequent operations
   - Expected: set.quiesce(41u64) equals `Ok(())`
   - Expected: set.phase() equals `MissionReadySetPhase.Quiesced`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quiesces terminally and rejects subsequent operations")
var set = ready_set(2u64)
expect(set.quiesce(41u64)).to_equal(Ok(()))
expect(set.phase()).to_equal(MissionReadySetPhase.Quiesced)
expect(set.admit(41u64, 0u64)).to_equal(
    Err(MissionReadySetError.NotReady))
expect(set.quiesce(41u64)).to_equal(
    Err(MissionReadySetError.AlreadyQuiesced))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering mission scalar ready set.
- mission scalar ready set

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

- Canonical SPipe generation for source `5ee819208af85f34d4e3b4ac5db9f6a1fc40dbb1a848cd40ef85eb9405f5cd1f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ee819208af85f34d4e3b4ac5db9f6a1fc40dbb1a848cd40ef85eb9405f5cd1f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ee819208af85f34d4e3b4ac5db9f6a1fc40dbb1a848cd40ef85eb9405f5cd1f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid owners and capacities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'seals once and reports only evidence the source can support' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut_noalloc/async/mission_ready_set_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits and wakes one exact slot without scanning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
