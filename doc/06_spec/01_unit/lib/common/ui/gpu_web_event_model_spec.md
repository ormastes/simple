# gpu_web_event_model_spec

> Purpose: Prove that GPU web event model — transaction contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_web_event_model_spec

Purpose: Prove that GPU web event model — transaction contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that GPU web event model — transaction contract.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### GPU web event model — transaction contract

#### should route a normalized packet deterministically through capture, target and bubble

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Normalize one pointer-down event against the current generation
   - Expected: batch.events.len() equals `1`
   - Expected: batch.rejects.len() equals `0`
- Build the journal over the three-phase listener set
- One transaction per listener, in capture -> target -> bubble order
   - Expected: journal.transactions.len() equals `3`
   - Expected: journal.transactions[0].phase equals `GPU_EVENT_PHASE_CAPTURE`
   - Expected: journal.transactions[0].handler_id equals `10u32`
   - Expected: journal.transactions[1].phase equals `GPU_EVENT_PHASE_TARGET`
   - Expected: journal.transactions[1].handler_id equals `11u32`
   - Expected: journal.transactions[2].phase equals `GPU_EVENT_PHASE_BUBBLE`
   - Expected: journal.transactions[2].handler_id equals `12u32`
- Mutation sequence numbers follow the same total order
   - Expected: journal.mutations.len() equals `4`
   - Expected: journal.mutations[0].sequence equals `0u32`
   - Expected: journal.mutations[3].sequence equals `3u32`
- The target handler's two writes keep write_index order
   - Expected: journal.transactions[1].mutation_start equals `1`
   - Expected: journal.transactions[1].mutation_count equals `2`
   - Expected: journal.mutations[1].operation equals `GPU_MUT_OP_SET`
   - Expected: journal.mutations[2].operation equals `GPU_MUT_OP_ADD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-COMMON-001
step("Normalize one pointer-down event against the current generation")
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch = gpu_event_normalize(raw, 4u64)
expect(batch.events.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(batch.rejects.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement

step("Build the journal over the three-phase listener set")
val journal = gpu_event_build_journal(batch, _targets(1u64, 2u32), _parents(),
    _listeners(), _staged(), _no_effects())

step("One transaction per listener, in capture -> target -> bubble order")
expect(journal.transactions.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(journal.transactions[0].phase).to_equal(GPU_EVENT_PHASE_CAPTURE)
expect(journal.transactions[0].handler_id).to_equal(10u32)
expect(journal.transactions[1].phase).to_equal(GPU_EVENT_PHASE_TARGET)
expect(journal.transactions[1].handler_id).to_equal(11u32)
expect(journal.transactions[2].phase).to_equal(GPU_EVENT_PHASE_BUBBLE)
expect(journal.transactions[2].handler_id).to_equal(12u32)

step("Mutation sequence numbers follow the same total order")
expect(journal.mutations.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(journal.mutations[0].sequence).to_equal(0u32)
expect(journal.mutations[3].sequence).to_equal(3u32)

step("The target handler's two writes keep write_index order")
expect(journal.transactions[1].mutation_start).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(journal.transactions[1].mutation_count).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(journal.mutations[1].operation).to_equal(GPU_MUT_OP_SET)
expect(journal.mutations[2].operation).to_equal(GPU_MUT_OP_ADD)
```

</details>

#### should replay a journal to the same state and the same epoch hash

- should replay a journal to the same state and the same epoch hash
- Apply the epoch once from empty state
   - Expected: first.accepted is true
   - Expected: first.mutations_applied equals `4`
- SET then ADD leaves 105 on the target node's field
   - Expected: gpu_node_state_read_lo(first.state, 2u32, 2u16) equals `105u32`
   - Expected: gpu_node_state_read_lo(first.state, 0u32, 1u16) equals `7u32`
   - Expected: gpu_node_state_read_lo(first.state, 1u32, 3u16) equals `4u32`
- Replay the same journal from empty state again
   - Expected: second.epoch_hash equals `first.epoch_hash`
   - Expected: gpu_node_state_read_lo(second.state, 2u32, 2u16) equals `105u32`
   - Expected: second.state.node_ids.len() equals `first.state.node_ids.len()`
- A committed epoch advances the scene generation exactly once
   - Expected: first.scene_generation_in equals `4u64`
   - Expected: first.scene_generation_out equals `5u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should replay a journal to the same state and the same epoch hash")
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch = gpu_event_normalize(raw, 4u64)
val journal = gpu_event_build_journal(batch, _targets(1u64, 2u32), _parents(),
    _listeners(), _staged(), _no_effects())

step("Apply the epoch once from empty state")
val first = gpu_event_epoch_apply(gpu_node_state_empty(), journal, _manifest(8, 2), 1u64)
expect(first.accepted).to_equal(true)
expect(first.mutations_applied).to_equal(4)  # oracle: 4 — named expected value from the requirement

step("SET then ADD leaves 105 on the target node's field")
expect(gpu_node_state_read_lo(first.state, 2u32, 2u16)).to_equal(105u32)
expect(gpu_node_state_read_lo(first.state, 0u32, 1u16)).to_equal(7u32)
expect(gpu_node_state_read_lo(first.state, 1u32, 3u16)).to_equal(4u32)

step("Replay the same journal from empty state again")
val second = gpu_event_epoch_apply(gpu_node_state_empty(), journal, _manifest(8, 2), 1u64)
expect(second.epoch_hash).to_equal(first.epoch_hash)
expect(gpu_node_state_read_lo(second.state, 2u32, 2u16)).to_equal(105u32)
expect(second.state.node_ids.len()).to_equal(first.state.node_ids.len())

step("A committed epoch advances the scene generation exactly once")
expect(first.scene_generation_in).to_equal(4u64)
expect(first.scene_generation_out).to_equal(5u64)
```

</details>

#### should reject an over-budget epoch and name the exceeded bound

- should reject an over-budget epoch and name the exceeded bound
- Admit only three mutations for an epoch that stages four
   - Expected: result.accepted is false
   - Expected: result.reason_code equals `GPU_EVENT_REJECT_CAPACITY`
   - Expected: result.breached_bound equals `max_mutations_per_epoch`
   - Expected: result.verdict.first_breach_bound equals `max_mutations_per_epoch`
   - Expected: result.verdict.breaches[0].requested equals `4`
   - Expected: result.verdict.breaches[0].limit equals `3`
- Nothing was applied and no generation was burned
   - Expected: result.mutations_applied equals `0`
   - Expected: result.state.node_ids.len() equals `0`
   - Expected: result.scene_generation_out equals `4u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject an over-budget epoch and name the exceeded bound")
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch = gpu_event_normalize(raw, 4u64)
val journal = gpu_event_build_journal(batch, _targets(1u64, 2u32), _parents(),
    _listeners(), _staged(), _no_effects())

step("Admit only three mutations for an epoch that stages four")
val result = gpu_event_epoch_apply(gpu_node_state_empty(), journal, _manifest(3, 2), 1u64)
expect(result.accepted).to_equal(false)
expect(result.reason_code).to_equal(GPU_EVENT_REJECT_CAPACITY)
expect(result.breached_bound).to_equal("max_mutations_per_epoch")
expect(result.verdict.first_breach_bound).to_equal("max_mutations_per_epoch")
expect(result.verdict.breaches[0].requested).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(result.verdict.breaches[0].limit).to_equal(3)  # oracle: 3 — named expected value from the requirement

step("Nothing was applied and no generation was burned")
expect(result.mutations_applied).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.state.node_ids.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.scene_generation_out).to_equal(4u64)
```

</details>

#### should reject an epoch whose host effects exceed the declared budget

- should reject an epoch whose host effects exceed the declared budget
   - Expected: journal.host_effects.len() equals `2`
- A one-effect budget rejects the epoch naming the host-effect bound
   - Expected: result.accepted is false
   - Expected: result.breached_bound equals `max_host_effects_per_epoch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject an epoch whose host effects exceed the declared budget")
var effects: [GpuStagedHostEffect] = []
effects = effects.push(GpuStagedHostEffect(handler_id: 11u32, write_index: 0u32,
    effect_kind: HOST_EFFECT_FETCH, continuation_id: 1u16,
    payload_offset: 0u32, payload_length: 12u32))
effects = effects.push(GpuStagedHostEffect(handler_id: 12u32, write_index: 0u32,
    effect_kind: HOST_EFFECT_FETCH, continuation_id: 2u16,
    payload_offset: 12u32, payload_length: 12u32))
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch = gpu_event_normalize(raw, 4u64)
val journal = gpu_event_build_journal(batch, _targets(1u64, 2u32), _parents(),
    _listeners(), _staged(), effects)
expect(journal.host_effects.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement

step("A one-effect budget rejects the epoch naming the host-effect bound")
val result = gpu_event_epoch_apply(gpu_node_state_empty(), journal, _manifest(8, 1), 1u64)
expect(result.accepted).to_equal(false)
expect(result.breached_bound).to_equal("max_host_effects_per_epoch")
```

</details>

#### should restore state exactly when an applied epoch is rolled back

- should restore state exactly when an applied epoch is rolled back
- Seed state with a first epoch, then apply a second over it
   - Expected: seeded.accepted is true
   - Expected: applied.accepted is true
   - Expected: gpu_node_state_read_lo(applied.state, 2u32, 2u16) equals `998u32`
   - Expected: gpu_node_state_read_lo(applied.state, 9u32, 5u16) equals `42u32`
- Rollback restores the overwritten value and drops the appended slot
   - Expected: gpu_node_state_read_lo(restored, 2u32, 2u16) equals `105u32`
   - Expected: gpu_node_state_read_lo(restored, 9u32, 5u16) equals `0u32`
   - Expected: restored.node_ids.len() equals `slots_before`
   - Expected: gpu_node_state_read_lo(restored, 0u32, 1u16) equals `7u32`
   - Expected: gpu_node_state_read_lo(restored, 1u32, 3u16) equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should restore state exactly when an applied epoch is rolled back")
step("Seed state with a first epoch, then apply a second over it")
var raw1: [GpuInputEvent] = []
raw1 = raw1.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch1 = gpu_event_normalize(raw1, 4u64)
val journal1 = gpu_event_build_journal(batch1, _targets(1u64, 2u32), _parents(),
    _listeners(), _staged(), _no_effects())
val seeded = gpu_event_epoch_apply(gpu_node_state_empty(), journal1, _manifest(8, 2), 1u64)
expect(seeded.accepted).to_equal(true)
val slots_before = seeded.state.node_ids.len()

var raw2: [GpuInputEvent] = []
raw2 = raw2.push(_ev(2u64, 5u64, GPU_EVENT_KIND_POINTER_DOWN, 11i32))
val batch2 = gpu_event_normalize(raw2, 5u64)
var second_staged: [GpuStagedMutation] = []
# overwrite an existing slot ...
second_staged = second_staged.push(GpuStagedMutation(handler_id: 11u32, write_index: 0u32,
    node_id: 2u32, node_generation: 1u32, field_id: 2u16,
    operation: GPU_MUT_OP_SET, value_lo: 999u32, value_hi: 0u32))
# ... twice, so rollback has to walk the undo log in reverse ...
second_staged = second_staged.push(GpuStagedMutation(handler_id: 11u32, write_index: 1u32,
    node_id: 2u32, node_generation: 1u32, field_id: 2u16,
    operation: GPU_MUT_OP_TOGGLE_BITS, value_lo: 1u32, value_hi: 0u32))
# ... and append a brand-new slot.
second_staged = second_staged.push(GpuStagedMutation(handler_id: 11u32, write_index: 2u32,
    node_id: 9u32, node_generation: 3u32, field_id: 5u16,
    operation: GPU_MUT_OP_SET, value_lo: 42u32, value_hi: 0u32))
var only_target: [GpuEventListener] = []
only_target = only_target.push(GpuEventListener(node_id: 2u32, phase: GPU_EVENT_PHASE_TARGET,
    registration_order: 0u32, handler_id: 11u32))
val journal2 = gpu_event_build_journal(batch2, _targets(2u64, 2u32), _parents(),
    only_target, second_staged, _no_effects())
val applied = gpu_event_epoch_apply(seeded.state, journal2, _manifest(8, 2), 2u64)
expect(applied.accepted).to_equal(true)
expect(gpu_node_state_read_lo(applied.state, 2u32, 2u16)).to_equal(998u32)
expect(gpu_node_state_read_lo(applied.state, 9u32, 5u16)).to_equal(42u32)

step("Rollback restores the overwritten value and drops the appended slot")
val restored = gpu_event_epoch_rollback(applied)
expect(gpu_node_state_read_lo(restored, 2u32, 2u16)).to_equal(105u32)
expect(gpu_node_state_read_lo(restored, 9u32, 5u16)).to_equal(0u32)
expect(restored.node_ids.len()).to_equal(slots_before)
expect(gpu_node_state_read_lo(restored, 0u32, 1u16)).to_equal(7u32)
expect(gpu_node_state_read_lo(restored, 1u32, 3u16)).to_equal(4u32)
```

</details>

#### should accept an empty input epoch without burning a scene generation

- should accept an empty input epoch without burning a scene generation
   - Expected: batch.events.len() equals `0`
   - Expected: batch.rejects.len() equals `0`
   - Expected: batch.input_count equals `0`
   - Expected: journal.transactions.len() equals `0`
   - Expected: journal.mutations.len() equals `0`
- An epoch with nothing to commit is accepted, not rejected
   - Expected: result.accepted is true
   - Expected: result.mutations_applied equals `0`
   - Expected: result.scene_generation_out equals `4u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should accept an empty input epoch without burning a scene generation")
val empty_raw: [GpuInputEvent] = []
val batch = gpu_event_normalize(empty_raw, 4u64)
expect(batch.events.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(batch.rejects.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(batch.input_count).to_equal(0)  # oracle: 0 — named expected value from the requirement

val empty_targets: [GpuEventTarget] = []
val journal = gpu_event_build_journal(batch, empty_targets, _parents(),
    _listeners(), _staged(), _no_effects())
expect(journal.transactions.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(journal.mutations.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement

step("An epoch with nothing to commit is accepted, not rejected")
val result = gpu_event_epoch_apply(gpu_node_state_empty(), journal, _manifest(8, 2), 1u64)
expect(result.accepted).to_equal(true)
expect(result.mutations_applied).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.scene_generation_out).to_equal(4u64)
```

</details>

#### should receipt every event it drops instead of dropping it silently

- should receipt every event it drops instead of dropping it silently
- Mix a stale-generation event, an unknown kind and a live event
   - Expected: batch.events.len() equals `1`
   - Expected: batch.rejects.len() equals `2`
   - Expected: batch.rejects[0].reason_code equals `GPU_EVENT_REJECT_STALE_SCENE_GENERATION`
   - Expected: batch.rejects[1].reason_code equals `GPU_EVENT_REJECT_UNKNOWN_KIND`
   - Expected: batch.rejects[0].node_id equals `DRAW_IR_V3_NO_ID`
- An event with no hit target is receipted, not routed
   - Expected: journal.mutations.len() equals `0`
   - Expected: _reject_count(journal, GPU_EVENT_REJECT_NO_TARGET) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should receipt every event it drops instead of dropping it silently")
step("Mix a stale-generation event, an unknown kind and a live event")
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(1u64, 3u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
raw = raw.push(_ev(2u64, 4u64, 900u16, 10i32))
raw = raw.push(_ev(3u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch = gpu_event_normalize(raw, 4u64)
expect(batch.events.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(batch.rejects.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(batch.rejects[0].reason_code).to_equal(GPU_EVENT_REJECT_STALE_SCENE_GENERATION)
expect(batch.rejects[1].reason_code).to_equal(GPU_EVENT_REJECT_UNKNOWN_KIND)
expect(batch.rejects[0].node_id).to_equal(DRAW_IR_V3_NO_ID)

step("An event with no hit target is receipted, not routed")
val no_targets: [GpuEventTarget] = []
val journal = gpu_event_build_journal(batch, no_targets, _parents(),
    _listeners(), _staged(), _no_effects())
expect(journal.mutations.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(_reject_count(journal, GPU_EVENT_REJECT_NO_TARGET)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### should receipt a listener whose handler has no GPU-side program

- should receipt a listener whose handler has no GPU-side program
- Route to a listener whose handler_id stages nothing
   - Expected: journal.transactions.len() equals `0`
   - Expected: _reject_count(journal, GPU_EVENT_REJECT_UNKNOWN_HANDLER) equals `1`
   - Expected: journal.rejects[0].handler_id equals `77u32`
- A route with no listener at all is receipted too
   - Expected: _reject_count(bare, GPU_EVENT_REJECT_NO_LISTENER) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should receipt a listener whose handler has no GPU-side program")
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch = gpu_event_normalize(raw, 4u64)

step("Route to a listener whose handler_id stages nothing")
var ls: [GpuEventListener] = []
ls = ls.push(GpuEventListener(node_id: 2u32, phase: GPU_EVENT_PHASE_TARGET,
    registration_order: 0u32, handler_id: 77u32))
val journal = gpu_event_build_journal(batch, _targets(1u64, 2u32), _parents(),
    ls, _staged(), _no_effects())
expect(journal.transactions.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(_reject_count(journal, GPU_EVENT_REJECT_UNKNOWN_HANDLER)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(journal.rejects[0].handler_id).to_equal(77u32)

step("A route with no listener at all is receipted too")
val no_listeners: [GpuEventListener] = []
val bare = gpu_event_build_journal(batch, _targets(1u64, 2u32), _parents(),
    no_listeners, _staged(), _no_effects())
expect(_reject_count(bare, GPU_EVENT_REJECT_NO_LISTENER)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### should reject an epoch that mutates a node whose generation moved on

- should reject an epoch that mutates a node whose generation moved on
   - Expected: seeded.accepted is true
- Stage a write against a node generation the state has moved past
   - Expected: result.accepted is false
   - Expected: result.reason_code equals `GPU_EVENT_REJECT_STALE_NODE_GENERATION`
- The seeded state is untouched by the rejected epoch
   - Expected: gpu_node_state_read_lo(result.state, 2u32, 2u16) equals `105u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject an epoch that mutates a node whose generation moved on")
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch = gpu_event_normalize(raw, 4u64)
val journal = gpu_event_build_journal(batch, _targets(1u64, 2u32), _parents(),
    _listeners(), _staged(), _no_effects())
val seeded = gpu_event_epoch_apply(gpu_node_state_empty(), journal, _manifest(8, 2), 1u64)
expect(seeded.accepted).to_equal(true)

step("Stage a write against a node generation the state has moved past")
var stale: [GpuStagedMutation] = []
stale = stale.push(GpuStagedMutation(handler_id: 11u32, write_index: 0u32,
    node_id: 2u32, node_generation: 99u32, field_id: 2u16,
    operation: GPU_MUT_OP_SET, value_lo: 1u32, value_hi: 0u32))
var only_target: [GpuEventListener] = []
only_target = only_target.push(GpuEventListener(node_id: 2u32, phase: GPU_EVENT_PHASE_TARGET,
    registration_order: 0u32, handler_id: 11u32))
var raw2: [GpuInputEvent] = []
raw2 = raw2.push(_ev(2u64, 5u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch2 = gpu_event_normalize(raw2, 5u64)
val journal2 = gpu_event_build_journal(batch2, _targets(2u64, 2u32), _parents(),
    only_target, stale, _no_effects())
val result = gpu_event_epoch_apply(seeded.state, journal2, _manifest(8, 2), 2u64)
expect(result.accepted).to_equal(false)
expect(result.reason_code).to_equal(GPU_EVENT_REJECT_STALE_NODE_GENERATION)

step("The seeded state is untouched by the rejected epoch")
expect(gpu_node_state_read_lo(result.state, 2u32, 2u16)).to_equal(105u32)
```

</details>

#### should reject an undefined mutation operation instead of ignoring it

- should reject an undefined mutation operation instead of ignoring it
- Verify: should reject an undefined mutation operation instead of ignoring it
   - Expected: result.accepted is false
   - Expected: result.state.node_ids.len() equals `0`
   - Expected: result.reason_code equals `GPU_EVENT_REJECT_UNSUPPORTED_OPERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject an undefined mutation operation instead of ignoring it")
step("Verify: should reject an undefined mutation operation instead of ignoring it")
var bad: [GpuStagedMutation] = []
bad = bad.push(GpuStagedMutation(handler_id: 11u32, write_index: 0u32,
    node_id: 2u32, node_generation: 1u32, field_id: 2u16,
    operation: GPU_MUT_OP_COUNT, value_lo: 1u32, value_hi: 0u32))
var only_target: [GpuEventListener] = []
only_target = only_target.push(GpuEventListener(node_id: 2u32, phase: GPU_EVENT_PHASE_TARGET,
    registration_order: 0u32, handler_id: 11u32))
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_DOWN, 10i32))
val batch = gpu_event_normalize(raw, 4u64)
val journal = gpu_event_build_journal(batch, _targets(1u64, 2u32), _parents(),
    only_target, bad, _no_effects())
val result = gpu_event_epoch_apply(gpu_node_state_empty(), journal, _manifest(8, 2), 1u64)
expect(result.accepted).to_equal(false)
expect(result.state.node_ids.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(result.reason_code).to_equal(GPU_EVENT_REJECT_UNSUPPORTED_OPERATION)
```

</details>

#### should coalesce pointer moves before the journal sees them

- should coalesce pointer moves before the journal sees them
- Arrival order is irrelevant; the packet is ordered by sequence
   - Expected: batch.input_count equals `3`
   - Expected: batch.events.len() equals `1`
   - Expected: batch.coalesced_count equals `2`
   - Expected: batch.events[0].sequence equals `3u64`
   - Expected: batch.events[0].x_fixed equals `30i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should coalesce pointer moves before the journal sees them")
var raw: [GpuInputEvent] = []
raw = raw.push(_ev(3u64, 4u64, GPU_EVENT_KIND_POINTER_MOVE, 30i32))
raw = raw.push(_ev(1u64, 4u64, GPU_EVENT_KIND_POINTER_MOVE, 10i32))
raw = raw.push(_ev(2u64, 4u64, GPU_EVENT_KIND_POINTER_MOVE, 20i32))
val batch = gpu_event_normalize(raw, 4u64)

step("Arrival order is irrelevant; the packet is ordered by sequence")
expect(batch.input_count).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(batch.events.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(batch.coalesced_count).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(batch.events[0].sequence).to_equal(3u64)
expect(batch.events[0].x_fixed).to_equal(30i32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `44733a822c6fa65504e7213a8e510547b8551fd4ecb08f04200be5407a15228d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44733a822c6fa65504e7213a8e510547b8551fd4ecb08f04200be5407a15228d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44733a822c6fa65504e7213a8e510547b8551fd4ecb08f04200be5407a15228d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/gpu_web_event_model_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/gpu_web_event_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/gpu_web_event_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:128:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route a normalized packet deterministically through capture, target and bubble' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route a normalized packet deterministically through capture, target and bubble' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:161:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should replay a journal to the same state and the same epoch hash' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should replay a journal to the same state and the same epoch hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:190:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an over-budget epoch and name the exceeded bound' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject an over-budget epoch and name the exceeded bound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:213:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an epoch whose host effects exceed the declared budget' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:235:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should restore state exactly when an applied epoch is rolled back' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_event_model_spec.spl:282:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept an empty input epoch without burning a scene generation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
