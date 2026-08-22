# wm_service_lifecycle_hardening_spec

> Verifies the wm service lifecycle hardening behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_service_lifecycle_hardening_spec

Verifies the wm service lifecycle hardening behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/wm/wm_service_lifecycle_hardening_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the wm service lifecycle hardening behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### WmService canonical lifecycle hardening

#### starts with a zero revision and bounded ingress queues

- Verify: starts with a zero revision and bounded ingress queues
   - Expected: wm.generation_value() equals `0u64`
   - Expected: wm.scene_revision_value() equals `0u64`
   - Expected: wm.focus_stack_value() equals `[]`
   - Expected: wm.max_action_queue_depth equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.max_input_queue_depth equals `256)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: starts with a zero revision and bounded ingress queues")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
expect(wm.generation_value()).to_equal(0u64)
expect(wm.scene_revision_value()).to_equal(0u64)
expect(wm.focus_stack_value()).to_equal([])
expect(wm.redraw_decision().accepted).to_be(false)
expect(wm.max_action_queue_depth).to_equal(64)  # oracle: pinned constant asserted by this scenario
expect(wm.max_input_queue_depth).to_equal(256)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects stale generation and stale scene revision before queueing

- Verify: rejects stale generation and stale scene revision before queueing
   - Expected: wm.last_rejection_reason equals `stale-lifecycle-generation`
   - Expected: wm.last_rejection_reason equals `stale-scene-revision`
   - Expected: wm.action_queue_depth equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: rejects stale generation and stale scene revision before queueing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
val a = action("focus", 7, 0, 0, 0, 0)
expect(wm.accept_action_ingress(1u64, 0u64, a)).to_be(false)
expect(wm.last_rejection_reason).to_equal("stale-lifecycle-generation")
expect(wm.accept_action_ingress(0u64, 1u64, a)).to_be(false)
expect(wm.last_rejection_reason).to_equal("stale-scene-revision")
expect(wm.action_queue_depth).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects invalid geometry and action queue overflow

- Verify: rejects invalid geometry and action queue overflow
   - Expected: wm.last_rejection_reason equals `invalid-geometry`
   - Expected: wm.last_rejection_reason equals `action-queue-overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: rejects invalid geometry and action queue overflow")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
val invalid = action("create_window", 0, 0, 0, 0, 900)
expect(wm.accept_action_ingress(0u64, 0u64, invalid)).to_be(false)
expect(wm.last_rejection_reason).to_equal("invalid-geometry")
wm.max_action_queue_depth = 1
val valid = action("create_window", 0, 0, 0, 640, 480)
expect(wm.accept_action_ingress(0u64, 0u64, valid)).to_be(true)
expect(wm.accept_action_ingress(0u64, 0u64, valid)).to_be(false)
expect(wm.last_rejection_reason).to_equal("action-queue-overflow")
expect(wm.complete_action_ingress()).to_be(true)
expect(wm.complete_action_ingress()).to_be(false)
```

</details>

#### rejects stale input, zero window input, and input queue overflow

- Verify: rejects stale input, zero window input, and input queue overflow
   - Expected: wm.last_rejection_reason equals `invalid-input-window`
   - Expected: wm.last_rejection_reason equals `unowned-input-window`
   - Expected: wm.last_rejection_reason equals `stale-input-sequence`
   - Expected: wm.last_rejection_reason equals `input-queue-overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: rejects stale input, zero window input, and input queue overflow")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
val zero_input = input(0u64)
expect(wm.accept_input_ingress(0u64, 1u64, zero_input)).to_be(false)
expect(wm.last_rejection_reason).to_equal("invalid-input-window")
val unowned_input = input(8u64)
expect(wm.accept_input_ingress(0u64, 1u64, unowned_input)).to_be(false)
expect(wm.last_rejection_reason).to_equal("unowned-input-window")
wm.register_window_owner(WindowId(value: 7u64), 7u64)
val event = input(7u64)
expect(wm.accept_input_ingress(0u64, 1u64, event)).to_be(true)
expect(wm.accept_input_ingress(0u64, 1u64, event)).to_be(false)
expect(wm.last_rejection_reason).to_equal("stale-input-sequence")
wm.complete_input_ingress()
wm.max_input_queue_depth = 1
expect(wm.accept_input_ingress(0u64, 2u64, event)).to_be(true)
expect(wm.accept_input_ingress(0u64, 3u64, event)).to_be(false)
expect(wm.last_rejection_reason).to_equal("input-queue-overflow")
```

</details>

#### admits input only for the focused owner without consuming a rejected sequence

- Verify: admits input only for the focused owner without consuming a rejected sequence
   - Expected: wm.focused_window() equals `7u64`
   - Expected: wm.last_rejection_reason equals `unfocused-input-window`
   - Expected: wm.last_input_sequence equals `0u64`
   - Expected: wm.input_queue_depth equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.focused_window() equals `8u64`
   - Expected: wm.last_rejection_reason equals `unfocused-input-window`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: admits input only for the focused owner without consuming a rejected sequence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 7u64), 70u64)
wm.register_window_owner(WindowId(value: 8u64), 80u64)
expect(wm.focused_window()).to_equal(7u64)
expect(wm.accept_input_ingress(0u64, 1u64, input(8u64))).to_be(false)
expect(wm.last_rejection_reason).to_equal("unfocused-input-window")
expect(wm.last_input_sequence).to_equal(0u64)
expect(wm.input_queue_depth).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(wm.accept_input_ingress(0u64, 1u64, input(7u64))).to_be(true)
expect(wm.complete_input_ingress()).to_be(true)
expect(wm.commit_focus(8u64)).to_be(true)
expect(wm.focused_window()).to_equal(8u64)
expect(wm.accept_input_ingress(0u64, 2u64, input(7u64))).to_be(false)
expect(wm.last_rejection_reason).to_equal("unfocused-input-window")
expect(wm.accept_input_ingress(0u64, 2u64, input(8u64))).to_be(true)
```

</details>

#### routes outbound admission through the same sequence and queue owner

- Verify: routes outbound admission through the same sequence and queue owner
   - Expected: wm.last_rejection_reason equals `unfocused-input-window`
   - Expected: wm.last_input_sequence equals `0u64`
   - Expected: wm.last_rejection_reason equals `input-window-mismatch`
   - Expected: wm.last_input_sequence equals `1u64`
   - Expected: wm.input_queue_depth equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.last_rejection_reason equals `input-sequence-exhausted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: routes outbound admission through the same sequence and queue owner")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 7u64), 70u64)
wm.register_window_owner(WindowId(value: 8u64), 80u64)
expect(wm.accept_next_input_ingress(8u64, input(8u64))).to_be(false)
expect(wm.last_rejection_reason).to_equal("unfocused-input-window")
expect(wm.last_input_sequence).to_equal(0u64)
expect(wm.accept_next_input_ingress(7u64, input(8u64))).to_be(false)
expect(wm.last_rejection_reason).to_equal("input-window-mismatch")
expect(wm.accept_next_input_ingress(7u64, input(7u64))).to_be(true)
expect(wm.last_input_sequence).to_equal(1u64)
expect(wm.input_queue_depth).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(wm.complete_input_ingress()).to_be(true)
wm.last_input_sequence = 18446744073709551615u64
expect(wm.accept_next_input_ingress(7u64, input(7u64))).to_be(false)
expect(wm.last_rejection_reason).to_equal("input-sequence-exhausted")
```

</details>

#### rejects unknown and non-owned actions and bounds combined action text

- Verify: rejects unknown and non-owned actions and bounds combined action text
   - Expected: wm.last_rejection_reason equals `unknown-action-kind`
   - Expected: wm.last_rejection_reason equals `invalid-action-window`
   - Expected: wm.last_rejection_reason equals `unowned-action-window`
   - Expected: wm.last_rejection_reason equals `action-text-too-large`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: rejects unknown and non-owned actions and bounds combined action text")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
val unknown = action("test_api", 0, 0, 0, 0, 0)
expect(wm.accept_action_ingress(0u64, 0u64, unknown)).to_be(false)
expect(wm.last_rejection_reason).to_equal("unknown-action-kind")
val zero_target = action("focus", 0, 0, 0, 0, 0)
expect(wm.accept_action_ingress(0u64, 0u64, zero_target)).to_be(false)
expect(wm.last_rejection_reason).to_equal("invalid-action-window")
val unowned_target = action("focus", 7u64, 0, 0, 0, 0)
expect(wm.accept_action_ingress(0u64, 0u64, unowned_target)).to_be(false)
expect(wm.last_rejection_reason).to_equal("unowned-action-window")
wm.register_window_owner(WindowId(value: 7u64), 7u64)
var oversized_text = action("update_tree", 7u64, 0, 0, 0, 0)
oversized_text.title = "t".repeat(40000)
oversized_text.content = "c".repeat(30000)
expect(wm.accept_action_ingress(0u64, wm.scene_revision_value(), oversized_text)).to_be(false)
expect(wm.last_rejection_reason).to_equal("action-text-too-large")
```

</details>

#### bounds committed input text before queue reservation

- Verify: bounds committed input text before queue reservation
   - Expected: wm.last_rejection_reason equals `input-text-too-large`
   - Expected: wm.input_queue_depth equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: bounds committed input text before queue reservation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 9u64), 9u64)
val oversized = WmInputEvent.text_input(WindowId(value: 9u64), "x".repeat(4097))
expect(wm.accept_input_ingress(0u64, 1u64, oversized)).to_be(false)
expect(wm.last_rejection_reason).to_equal("input-text-too-large")
expect(wm.input_queue_depth).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects stale, invalid, and over-capacity redraw candidates

- Verify: rejects stale, invalid, and over-capacity redraw candidates
   - Expected: stale_result.reason equals `stale-damage-generation`
   - Expected: stale_revision_result.reason equals `stale-damage-revision`
   - Expected: invalid_result.reason equals `invalid-damage-geometry`
   - Expected: oversized_reason_result.reason equals `damage-reason-too-large`
   - Expected: overflow_result.reason equals `damage-region-overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: rejects stale, invalid, and over-capacity redraw candidates")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val stale = WmDamageRegionV1(
    generation: 1u64,
    scene_revision: 1u64,
    full_redraw: false,
    reason: "input",
    rects: [WmDamageRectV1(x: 0, y: 0, width: 8, height: 8)]
)
val stale_result = wm_damage_admit_v1(stale, 0u64, 1u64)
expect(stale_result.accepted).to_be(false)
expect(stale_result.reason).to_equal("stale-damage-generation")
val stale_revision = WmDamageRegionV1(
    generation: 0u64,
    scene_revision: 2u64,
    full_redraw: true,
    reason: "focus",
    rects: []
)
val stale_revision_result = wm_damage_admit_v1(stale_revision, 0u64, 1u64)
expect(stale_revision_result.accepted).to_be(false)
expect(stale_revision_result.reason).to_equal("stale-damage-revision")
val invalid = WmDamageRegionV1(
    generation: 0u64,
    scene_revision: 1u64,
    full_redraw: false,
    reason: "resize",
    rects: [WmDamageRectV1(x: 0, y: 0, width: 0, height: 8)]
)
val invalid_result = wm_damage_admit_v1(invalid, 0u64, 1u64)
expect(invalid_result.accepted).to_be(false)
expect(invalid_result.reason).to_equal("invalid-damage-geometry")
val oversized_reason = WmDamageRegionV1(
    generation: 0u64,
    scene_revision: 1u64,
    full_redraw: true,
    reason: "r".repeat(65),
    rects: []
)
val oversized_reason_result = wm_damage_admit_v1(oversized_reason, 0u64, 1u64)
expect(oversized_reason_result.accepted).to_be(false)
expect(oversized_reason_result.reason).to_equal("damage-reason-too-large")
var many_rects: [WmDamageRectV1] = []
var i: i32 = 0
while i < 65:
    many_rects = many_rects.push(WmDamageRectV1(x: i, y: 0, width: 1, height: 1))
    i = i + 1
val overflow = WmDamageRegionV1(
    generation: 0u64,
    scene_revision: 1u64,
    full_redraw: false,
    reason: "input",
    rects: many_rects
)
val overflow_result = wm_damage_admit_v1(overflow, 0u64, 1u64)
expect(overflow_result.accepted).to_be(false)
expect(overflow_result.reason).to_equal("damage-region-overflow")
```

</details>

#### clips off-screen damage and transitively coalesces touching regions

- Verify: clips off-screen damage and transitively coalesces touching regions
   - Expected: normalized.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: normalized[0].x equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: normalized[0].y equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: normalized[0].width equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: normalized[0].height equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.damage_clip_width equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.last_rejection_reason equals `invalid-damage-bounds`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: clips off-screen damage and transitively coalesces touching regions")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val normalized = wm_damage_merge_rects_v1(
    [
        WmDamageRectV1(x: -5, y: -4, width: 10, height: 10),
        WmDamageRectV1(x: 5, y: 0, width: 10, height: 10)
    ],
    [
        WmDamageRectV1(x: 14, y: 0, width: 20, height: 10),
        WmDamageRectV1(x: 80, y: 80, width: 10, height: 10)
    ],
    20,
    20
)
expect(normalized.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(normalized[0].x).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(normalized[0].y).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(normalized[0].width).to_equal(20)  # oracle: pinned constant asserted by this scenario
expect(normalized[0].height).to_equal(10)  # oracle: pinned constant asserted by this scenario

val wm = WmService.new()
expect(wm.set_damage_bounds(20, 20)).to_be(true)
wm.register_window_owner(WindowId(value: 22u64), 220u64)
expect(wm.damage_clip_width).to_equal(20)  # oracle: pinned constant asserted by this scenario
expect(wm.set_damage_bounds(0, 20)).to_be(false)
expect(wm.last_rejection_reason).to_equal("invalid-damage-bounds")
```

</details>

#### keeps lifecycle and owner state intact when restart generation cannot advance

- Verify: keeps lifecycle and owner state intact when restart generation cannot advance
   - Expected: wm.restart() equals `0u64`
   - Expected: wm.window_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.focused_window() equals `21u64`
   - Expected: wm.last_rejection_reason equals `lifecycle-generation-exhausted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: keeps lifecycle and owner state intact when restart generation cannot advance")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 21u64), 210u64)
wm.running = true
wm.lifecycle_generation = 18446744073709551615u64
expect(wm.restart()).to_equal(0u64)
expect(wm.running).to_be(true)
expect(wm.window_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(wm.focused_window()).to_equal(21u64)
expect(wm.last_rejection_reason).to_equal("lifecycle-generation-exhausted")
```

</details>

#### fails closed when scene revision reaches its maximum

- Verify: fails closed when scene revision reaches its maximum
   - Expected: wm.owner_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.world.live_window_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.last_rejection_reason equals `scene-revision-exhausted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: fails closed when scene revision reaches its maximum")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.scene_revision = 18446744073709551615u64
wm.register_window_owner(WindowId(value: 11u64), 11u64)
expect(wm.owner_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(wm.world.live_window_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(wm.last_rejection_reason).to_equal("scene-revision-exhausted")
```

</details>

#### rejects owner conflicts, unsafe app ids, and widened fixed capacity

- Verify: rejects owner conflicts, unsafe app ids, and widened fixed capacity
   - Expected: wm.find_owner(12u64) equals `40u64`
   - Expected: wm.last_rejection_reason equals `owner-port-conflict`
   - Expected: wm.find_owner(13u64) equals `0u64`
   - Expected: wm.last_rejection_reason equals `invalid-app-id`
   - Expected: wm.last_rejection_reason equals `window-owner-capacity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: rejects owner conflicts, unsafe app ids, and widened fixed capacity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.register_window_owner_with_identity(WindowId(value: 12u64), 40u64, 50u64, "app.safe")
wm.register_window_owner_with_identity(WindowId(value: 12u64), 41u64, 51u64, "app.hijack")
expect(wm.find_owner(12u64)).to_equal(40u64)
expect(wm.last_rejection_reason).to_equal("owner-port-conflict")
wm.register_window_owner_with_identity(WindowId(value: 13u64), 42u64, 52u64, "bad\napp")
expect(wm.find_owner(13u64)).to_equal(0u64)
expect(wm.last_rejection_reason).to_equal("invalid-app-id")
wm.max_windows = 300
wm.owner_count = 256
wm.register_window_owner(WindowId(value: 14u64), 43u64)
expect(wm.last_rejection_reason).to_equal("window-owner-capacity")
```

</details>

#### fails closed before request count wrap and restart recovers the counter

- Verify: fails closed before request count wrap and restart recovers the counter
   - Expected: wm.last_rejection_reason equals `request-count-exhausted`
   - Expected: wm.restart() equals `1u64`
   - Expected: wm.request_count equals `0u64`
   - Expected: wm.request_count equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: fails closed before request count wrap and restart recovers the counter")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.request_count = 18446744073709551615u64
expect(wm.record_request()).to_be(false)
expect(wm.last_rejection_reason).to_equal("request-count-exhausted")
expect(wm.restart()).to_equal(1u64)
expect(wm.request_count).to_equal(0u64)
expect(wm.record_request()).to_be(true)
expect(wm.request_count).to_equal(1u64)
```

</details>

#### cleans owner-dead ECS windows and focuses the next stack-top window

- Verify: cleans owner-dead ECS windows and focuses the next stack-top window
   - Expected: wm.focus_stack_value() equals `[30u64, 10u64, 20u64]`
   - Expected: wm.focus_stack_value() equals `[10u64, 20u64, 30u64]`
   - Expected: wm.focused_window() equals `30u64`
   - Expected: wm.world.live_window_count() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: removed.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: removed[0] equals `30u64`
   - Expected: wm.world.live_window_count() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.window_count() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.focused_window() equals `20u64`
   - Expected: wm.focus_stack_value() equals `[10u64, 20u64]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: cleans owner-dead ECS windows and focuses the next stack-top window")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 30u64), 30u64)
wm.register_window_owner(WindowId(value: 10u64), 10u64)
wm.register_window_owner(WindowId(value: 20u64), 20u64)
expect(wm.focus_stack_value()).to_equal([30u64, 10u64, 20u64])
expect(wm.raise_focus_stack(30u64)).to_be(true)
expect(wm.focus_stack_value()).to_equal([10u64, 20u64, 30u64])
expect(wm.focused_window()).to_equal(30u64)
expect(wm.world.live_window_count()).to_equal(3)  # oracle: pinned constant asserted by this scenario
val removed = wm.remove_all_windows_for_port(30u64)
expect(removed.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(removed[0]).to_equal(30u64)
expect(wm.world.live_window_count()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(wm.window_count()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(wm.focused_window()).to_equal(20u64)
expect(wm.focus_stack_value()).to_equal([10u64, 20u64])
expect(wm.redraw_decision().accepted).to_be(true)
expect(wm.redraw_decision().full_redraw).to_be(true)
```

</details>

#### fences old ingress after restart and clears presentation state

- Verify: fences old ingress after restart and clears presentation state
   - Expected: next_generation equals `1u64`
   - Expected: wm.window_count() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: wm.focus_stack_value() equals `[]`
   - Expected: wm.last_presented_frame_id equals `0u64`
   - Expected: wm.last_readback_source equals ``
   - Expected: wm.last_rejection_reason equals `stale-lifecycle-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: fences old ingress after restart and clears presentation state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 3u64), 3u64)
val old_generation = wm.generation_value()
val revision = wm.scene_revision_value()
val a = action("focus", 3, 0, 0, 0, 0)
expect(wm.accept_action_ingress(old_generation, revision, a)).to_be(true)
val next_generation = wm.restart()
expect(next_generation).to_equal(1u64)
expect(wm.window_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(wm.focus_stack_value()).to_equal([])
expect(wm.redraw_decision().accepted).to_be(false)
expect(wm.last_presented_frame_id).to_equal(0u64)
expect(wm.last_readback_source).to_equal("")
expect(wm.accept_action_ingress(old_generation, revision, a)).to_be(false)
expect(wm.last_rejection_reason).to_equal("stale-lifecycle-generation")
wm.register_window_owner(WindowId(value: 3u64), 3u64)
expect(wm.accept_action_ingress(next_generation, wm.scene_revision_value(), a)).to_be(true)
```

</details>

#### accepts only current nonzero frame/readback receipts and correlates them immutably

- Verify: accepts only current nonzero frame/readback receipts and correlates them immutably
   - Expected: wm.last_rejection_reason equals `fabricated-frame-or-readback`
   - Expected: wm.last_rejection_reason equals `invalid-readback-source`
   - Expected: wm.last_rejection_reason equals `stale-frame-id`
   - Expected: wm.last_rejection_reason equals `stale-scene-revision`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-017 REQ-019
step("Verify: accepts only current nonzero frame/readback receipts and correlates them immutably")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val wm = WmService.new()
wm.register_window_owner(WindowId(value: 8u64), 8u64)
val generation = wm.generation_value()
val revision = wm.scene_revision_value()
expect(wm.commit_presentation(generation, revision, 0u64, 44u64, "framebuffer")).to_be(false)
expect(wm.last_rejection_reason).to_equal("fabricated-frame-or-readback")
expect(wm.commit_presentation(generation, revision, 1u64, 44u64, "cpu_mirror")).to_be(false)
expect(wm.last_rejection_reason).to_equal("invalid-readback-source")
expect(wm.commit_presentation(generation, revision, 1u64, 44u64, "framebuffer")).to_be(true)
expect(wm.redraw_decision().accepted).to_be(false)
expect(wm.presentation_matches(generation, revision, 1u64, 44u64, "framebuffer")).to_be(true)
expect(wm.presentation_matches(generation, revision, 1u64, 44u64, "device_readback")).to_be(false)
expect(wm.commit_presentation(generation, revision, 1u64, 45u64, "framebuffer")).to_be(false)
expect(wm.last_rejection_reason).to_equal("stale-frame-id")
expect(wm.commit_presentation(generation, revision - 1u64, 2u64, 46u64, "framebuffer")).to_be(false)
expect(wm.last_rejection_reason).to_equal("stale-scene-revision")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca204af91529913aba018ef52ba46212176bc5aa8489e7ab1574e7a324c94878`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca204af91529913aba018ef52ba46212176bc5aa8489e7ab1574e7a324c94878`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca204af91529913aba018ef52ba46212176bc5aa8489e7ab1574e7a324c94878`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/services/wm/wm_service_lifecycle_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/services/wm/wm_service_lifecycle_hardening_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/wm/wm_service_lifecycle_hardening_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/services/wm/wm_service_lifecycle_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/wm/wm_service_lifecycle_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
