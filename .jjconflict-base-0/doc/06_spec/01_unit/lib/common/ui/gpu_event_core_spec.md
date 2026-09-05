# GPU Event Core Spec

> `gpu_event_core.spl` is the CPU-reference interpreter for the W2 "GPU event core" described in `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` §3 "GPU event model" and §11 W2. It operates on the frozen C0 packet types from `gpu_web_ports.spl` (`GpuInputEvent`, `GpuMutation`) and implements, in pure Simple with no Dict, the deterministic pieces of the per-event pipeline: stale-generation rejection, pointer-move/wheel coalescing, ancestor route construction, capture/target/bubble dispatch ordering, mutation journal commit ordering, and a deterministic epoch hash used as an oracle handle for "same event batch produces deterministic mutation bytes".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Event Core Spec

`gpu_event_core.spl` is the CPU-reference interpreter for the W2 "GPU event core" described in `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` §3 "GPU event model" and §11 W2. It operates on the frozen C0 packet types from `gpu_web_ports.spl` (`GpuInputEvent`, `GpuMutation`) and implements, in pure Simple with no Dict, the deterministic pieces of the per-event pipeline: stale-generation rejection, pointer-move/wheel coalescing, ancestor route construction, capture/target/bubble dispatch ordering, mutation journal commit ordering, and a deterministic epoch hash used as an oracle handle for "same event batch produces deterministic mutation bytes".

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md |
| Design | doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md §3, §11 W2 |
| Research | N/A |
| Source | `test/01_unit/lib/common/ui/gpu_event_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`gpu_event_core.spl` is the CPU-reference interpreter for the W2 "GPU event
core" described in
`doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` §3 "GPU event
model" and §11 W2. It operates on the frozen C0 packet types from
`gpu_web_ports.spl` (`GpuInputEvent`, `GpuMutation`) and implements, in pure
Simple with no Dict, the deterministic pieces of the per-event pipeline:
stale-generation rejection, pointer-move/wheel coalescing, ancestor route
construction, capture/target/bubble dispatch ordering, mutation journal
commit ordering, and a deterministic epoch hash used as an oracle handle for
"same event batch produces deterministic mutation bytes".

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md

## Design

**Design:** doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md §3, §11 W2

## Research

**Research:** N/A

## Examples

Each example below exercises one deterministic-ordering guarantee the plan
requires of the CPU reference: stale events never validate, moves/wheels
coalesce while other kinds pass through untouched, an ancestor route walks
root-to-target, dispatch visits capture/target/bubble in the documented
order with registration_order as the tie-break, the mutation journal is a
stable sort by sequence, and the epoch hash is a pure function of mutation
field bytes.

## Scenarios

### gpu_event_validate_generation -- stale-event rejection

#### accepts an event whose scene_generation matches current, rejects a stale one

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts an event whose scene_generation matches current, rejects a stale one
- Build one event pinned to generation 5
- Validate against the matching generation
- Validate against a newer generation: must reject


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts an event whose scene_generation matches current, rejects a stale one")
step("Build one event pinned to generation 5")
val ev = mk_event(1u64, 5u64, GPU_EVENT_KIND_POINTER_DOWN, 0, 0, 0, 0)

step("Validate against the matching generation")
assert_true(gpu_event_validate_generation(ev, 5u64))

step("Validate against a newer generation: must reject")
assert_false(gpu_event_validate_generation(ev, 6u64))
```

</details>

### gpu_event_coalesce -- pointer-move and wheel merging

#### merges 3 consecutive POINTER_MOVE events into 1, keeping the last position

- merges 3 consecutive POINTER_MOVE events into 1, keeping the last position
- Build 3 consecutive moves ending at (3, 3)
- Coalesce: expect exactly 1 event with the last position
   - Expected: merged[0].x_fixed equals `3`
   - Expected: merged[0].y_fixed equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges 3 consecutive POINTER_MOVE events into 1, keeping the last position")
step("Build 3 consecutive moves ending at (3, 3)")
val events = [
    mk_event(1u64, 1u64, GPU_EVENT_KIND_POINTER_MOVE, 1, 1, 0, 0),
    mk_event(2u64, 1u64, GPU_EVENT_KIND_POINTER_MOVE, 2, 2, 0, 0),
    mk_event(3u64, 1u64, GPU_EVENT_KIND_POINTER_MOVE, 3, 3, 0, 0),
]

step("Coalesce: expect exactly 1 event with the last position")
val merged = gpu_event_coalesce(events)
assert_equal(merged.len(), 1)
expect(merged[0].x_fixed).to_equal(3)
expect(merged[0].y_fixed).to_equal(3)
```

</details>

#### sums delta_x_fixed/delta_y_fixed across a consecutive WHEEL run

- sums delta_x_fixed/delta_y_fixed across a consecutive WHEEL run
- Build 2 consecutive wheel events
- Coalesce: expect 1 event with summed deltas
   - Expected: merged[0].delta_x_fixed equals `4`
   - Expected: merged[0].delta_y_fixed equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sums delta_x_fixed/delta_y_fixed across a consecutive WHEEL run")
step("Build 2 consecutive wheel events")
val events = [
    mk_event(1u64, 1u64, GPU_EVENT_KIND_WHEEL, 0, 0, 1, 2),
    mk_event(2u64, 1u64, GPU_EVENT_KIND_WHEEL, 0, 0, 3, 4),
]

step("Coalesce: expect 1 event with summed deltas")
val merged = gpu_event_coalesce(events)
assert_equal(merged.len(), 1)
expect(merged[0].delta_x_fixed).to_equal(4)
expect(merged[0].delta_y_fixed).to_equal(6)
```

</details>

#### passes non-coalescible kinds through unchanged and in order

- passes non-coalescible kinds through unchanged and in order
- Build a down/key/up sequence -- none of these kinds coalesce
- Coalesce: expect all 3 preserved, relative order intact
   - Expected: merged[0].sequence equals `10u64`
   - Expected: merged[1].sequence equals `11u64`
   - Expected: merged[2].sequence equals `12u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes non-coalescible kinds through unchanged and in order")
step("Build a down/key/up sequence -- none of these kinds coalesce")
val events = [
    mk_event(10u64, 1u64, GPU_EVENT_KIND_POINTER_DOWN, 0, 0, 0, 0),
    mk_event(11u64, 1u64, GPU_EVENT_KIND_KEY_DOWN, 0, 0, 0, 0),
    mk_event(12u64, 1u64, GPU_EVENT_KIND_POINTER_UP, 0, 0, 0, 0),
]

step("Coalesce: expect all 3 preserved, relative order intact")
val merged = gpu_event_coalesce(events)
assert_equal(merged.len(), 3)
expect(merged[0].sequence).to_equal(10u64)
expect(merged[1].sequence).to_equal(11u64)
expect(merged[2].sequence).to_equal(12u64)
```

</details>

### gpu_event_build_route -- ancestor chain

#### builds a root-to-target chain for a 3-deep parent hierarchy

- builds a root-to-target chain for a 3-deep parent hierarchy
- node 0 is root (parents[0] == 0), node 1's parent is 0, node 2's parent is 1
- Build the route to target node 2
   - Expected: route[0] equals `0u32`
   - Expected: route[1] equals `1u32`
   - Expected: route[2] equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds a root-to-target chain for a 3-deep parent hierarchy")
step("node 0 is root (parents[0] == 0), node 1's parent is 0, node 2's parent is 1")
val parents = [0u32, 0u32, 1u32]

step("Build the route to target node 2")
val route = gpu_event_build_route(2u32, parents)
assert_equal(route.len(), 3)
expect(route[0]).to_equal(0u32)
expect(route[1]).to_equal(1u32)
expect(route[2]).to_equal(2u32)
```

</details>

### gpu_event_dispatch -- capture/target/bubble order

#### visits capture(root, mid) -> target -> bubble(mid, root), tie-breaking by registration_order

- visits capture(root, mid) -> target -> bubble(mid, root), tie-breaking by registration_order
- 3-deep chain: root=0, mid=1, target=2
- Register 2 capture listeners on root out of registration_order, plus 1 each on mid/target/mid-bubble/root-bubble
- Dispatch to target node 2
- Expect: root-capture(order1), root-capture(order5), mid-capture, target, mid-bubble, root-bubble
   - Expected: steps[0].listener_handler_id equals `101u32`
   - Expected: steps[1].listener_handler_id equals `100u32`
   - Expected: steps[2].listener_handler_id equals `102u32`
   - Expected: steps[3].listener_handler_id equals `103u32`
   - Expected: steps[4].listener_handler_id equals `104u32`
   - Expected: steps[5].listener_handler_id equals `105u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("visits capture(root, mid) -> target -> bubble(mid, root), tie-breaking by registration_order")
step("3-deep chain: root=0, mid=1, target=2")
val parents = [0u32, 0u32, 1u32]

step("Register 2 capture listeners on root out of registration_order, plus 1 each on mid/target/mid-bubble/root-bubble")
val listeners = [
    GpuEventListener(node_id: 0u32, phase: 0u16, registration_order: 5u32, handler_id: 100u32),
    GpuEventListener(node_id: 0u32, phase: 0u16, registration_order: 1u32, handler_id: 101u32),
    GpuEventListener(node_id: 1u32, phase: 0u16, registration_order: 1u32, handler_id: 102u32),
    GpuEventListener(node_id: 2u32, phase: 1u16, registration_order: 1u32, handler_id: 103u32),
    GpuEventListener(node_id: 1u32, phase: 2u16, registration_order: 1u32, handler_id: 104u32),
    GpuEventListener(node_id: 0u32, phase: 2u16, registration_order: 1u32, handler_id: 105u32),
]

step("Dispatch to target node 2")
val steps = gpu_event_dispatch(2u32, parents, listeners)

step("Expect: root-capture(order1), root-capture(order5), mid-capture, target, mid-bubble, root-bubble")
assert_equal(steps.len(), 6)
expect(steps[0].listener_handler_id).to_equal(101u32)
expect(steps[1].listener_handler_id).to_equal(100u32)
expect(steps[2].listener_handler_id).to_equal(102u32)
expect(steps[3].listener_handler_id).to_equal(103u32)
expect(steps[4].listener_handler_id).to_equal(104u32)
expect(steps[5].listener_handler_id).to_equal(105u32)
```

</details>

### gpu_mutation_journal_commit -- stable sort by sequence

#### sorts by sequence and preserves insertion order among equal sequences

- sorts by sequence and preserves insertion order among equal sequences
- Build 4 mutations with sequences 2, 1, 1, 0 (2 ties at sequence 1)
- Commit the journal
   - Expected: journal[0].node_id equals `30u32`
   - Expected: journal[1].node_id equals `20u32`
   - Expected: journal[2].node_id equals `21u32`
   - Expected: journal[3].node_id equals `10u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sorts by sequence and preserves insertion order among equal sequences")
step("Build 4 mutations with sequences 2, 1, 1, 0 (2 ties at sequence 1)")
val mutations = [
    mk_mutation(10u32, 0u32, 0u16, 0u16, 0u32, 0u32, 2u32),
    mk_mutation(20u32, 0u32, 0u16, 0u16, 0u32, 0u32, 1u32),
    mk_mutation(21u32, 0u32, 0u16, 0u16, 0u32, 0u32, 1u32),
    mk_mutation(30u32, 0u32, 0u16, 0u16, 0u32, 0u32, 0u32),
]

step("Commit the journal")
val journal = gpu_mutation_journal_commit(mutations)
assert_equal(journal.len(), 4)
expect(journal[0].node_id).to_equal(30u32)
expect(journal[1].node_id).to_equal(20u32)
expect(journal[2].node_id).to_equal(21u32)
expect(journal[3].node_id).to_equal(10u32)
```

</details>

### gpu_event_epoch_hash -- deterministic mutation bytes

#### hashes identical batches equal, and a changed field to a different value

- hashes identical batches equal, and a changed field to a different value
- Build 2 separately-constructed but field-identical batches
- Equal field batches must hash equal
   - Expected: gpu_event_epoch_hash(batch_a) equals `gpu_event_epoch_hash(batch_b)`
- Changing one field (value_lo) must change the hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes identical batches equal, and a changed field to a different value")
step("Build 2 separately-constructed but field-identical batches")
val batch_a = [mk_mutation(1u32, 2u32, 3u16, 4u16, 5u32, 6u32, 7u32)]
val batch_b = [mk_mutation(1u32, 2u32, 3u16, 4u16, 5u32, 6u32, 7u32)]

step("Equal field batches must hash equal")
expect(gpu_event_epoch_hash(batch_a)).to_equal(gpu_event_epoch_hash(batch_b))

step("Changing one field (value_lo) must change the hash")
val batch_c = [mk_mutation(1u32, 2u32, 3u16, 4u16, 9u32, 6u32, 7u32)]
val hash_a = gpu_event_epoch_hash(batch_a)
val hash_c = gpu_event_epoch_hash(batch_c)
assert_true(hash_a != hash_c)
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


## Related Documentation

- **Plan:** `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md`
- **Design:** `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md §3, §11 W2`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `710dc346596a619d01d7e6a752e42edd0c6cb9f49723c69d2f42b28c514ad1e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `710dc346596a619d01d7e6a752e42edd0c6cb9f49723c69d2f42b28c514ad1e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `710dc346596a619d01d7e6a752e42edd0c6cb9f49723c69d2f42b28c514ad1e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/gpu_event_core_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/gpu_event_core_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/gpu_event_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/gpu_event_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/gpu_event_core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/gpu_event_core_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an event whose scene_generation matches current, rejects a stale one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_event_core_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'merges 3 consecutive POINTER_MOVE events into 1, keeping the last position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_event_core_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums delta_x_fixed/delta_y_fixed across a consecutive WHEEL run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
