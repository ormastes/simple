# Ui Scene Event Route Specification

> Tests covering ui_scene_route_event component identity (design section 9, gate a), ui_scene_route_event stale generation (design section 9, gate b), ui_scene_route_event no-hit and no-owner refusals, ui_scene_route_event hidden-group hit exclusion (design section 4.1, gate d), ui_scene_route_event nested WebView chain (design section 4.1/research section 7, gate c), ui_scene_route_event composes with menu-action dispatch validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Scene Event Route Specification

## Scenarios

### ui_scene_route_event component identity (design section 9, gate a)

#### routes a hit to the exact component_id shared by the command, its hit shape and its owner

- routes a hit to the exact component_id shared by the command, its hit shape and its owner
   - Expected: receipt.accepted is true
   - Expected: receipt.reason equals `UI_SCENE_ROUTE_OK`
   - Expected: receipt.hit_component_id equals `scene.commands[0].component_id`
   - Expected: receipt.hit_component_id equals `5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes a hit to the exact component_id shared by the command, its hit shape and its owner")
val scene = _l9_button_scene(5u32, 0u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = [_l9_owner(5u32, 0u32, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID)]
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(true)
expect(receipt.reason).to_equal(UI_SCENE_ROUTE_OK)
expect(receipt.hit_component_id).to_equal(scene.commands[0].component_id)
expect(receipt.hit_component_id).to_equal(5u32)
_l9_expect_chain(receipt.owner_chain, [0u32])
print "l9_route_identity hit={receipt.hit_component_id} chain_len={receipt.owner_chain.len()}"
```

</details>

### ui_scene_route_event stale generation (design section 9, gate b)

#### refuses a hit whose command generation no longer matches the owner table's current generation

- refuses a hit whose command generation no longer matches the owner table's current generation
   - Expected: receipt.accepted is false
   - Expected: receipt.reason equals `UI_SCENE_ROUTE_REFUSE_STALE_GENERATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a hit whose command generation no longer matches the owner table's current generation")
val scene = _l9_button_scene(5u32, 1u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = [_l9_owner(5u32, 0u32, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID)]
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(false)
expect(receipt.reason).to_equal(UI_SCENE_ROUTE_REFUSE_STALE_GENERATION)
print "l9_route_stale_generation reason={receipt.reason}"
```

</details>

#### delivers an empty owner chain and NO_ID action on a stale-generation refusal (never a partial delivery)

- delivers an empty owner chain and NO_ID action on a stale-generation refusal (never a partial delivery)
   - Expected: receipt.accepted is false
   - Expected: receipt.owner_chain.len() equals `0`
   - Expected: receipt.action_binding_id equals `DRAW_IR_V3_NO_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("delivers an empty owner chain and NO_ID action on a stale-generation refusal (never a partial delivery)")
val scene = _l9_button_scene(5u32, 2u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = [_l9_owner(5u32, 0u32, DRAW_IR_V3_NO_ID, 9u32)]
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(false)
expect(receipt.owner_chain.len()).to_equal(0)
expect(receipt.action_binding_id).to_equal(DRAW_IR_V3_NO_ID)
```

</details>

### ui_scene_route_event no-hit and no-owner refusals

#### refuses with NO_HIT for a point outside every hit shape

- refuses with NO_HIT for a point outside every hit shape
   - Expected: receipt.accepted is false
   - Expected: receipt.reason equals `UI_SCENE_ROUTE_REFUSE_NO_HIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses with NO_HIT for a point outside every hit shape")
val scene = _l9_button_scene(5u32, 0u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = [_l9_owner(5u32, 0u32, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID)]
val receipt = ui_scene_route_event(scene, resolved, owners, 500, 500)
expect(receipt.accepted).to_equal(false)
expect(receipt.reason).to_equal(UI_SCENE_ROUTE_REFUSE_NO_HIT)
```

</details>

#### refuses with NO_OWNER for a hit whose component_id has no owner record

- refuses with NO_OWNER for a hit whose component_id has no owner record
   - Expected: receipt.accepted is false
   - Expected: receipt.reason equals `UI_SCENE_ROUTE_REFUSE_NO_OWNER`
   - Expected: receipt.hit_component_id equals `5u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses with NO_OWNER for a hit whose component_id has no owner record")
val scene = _l9_button_scene(5u32, 0u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val receipt = ui_scene_route_event(scene, resolved, [], 5, 5)
expect(receipt.accepted).to_equal(false)
expect(receipt.reason).to_equal(UI_SCENE_ROUTE_REFUSE_NO_OWNER)
expect(receipt.hit_component_id).to_equal(5u32)
```

</details>

#### reports NO_ID hit_component_id on a NO_HIT refusal, distinct from a NO_OWNER refusal which still reports it

- reports NO_ID hit_component_id on a NO_HIT refusal, distinct from a NO_OWNER refusal which still reports it
   - Expected: receipt.hit_component_id equals `DRAW_IR_V3_NO_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports NO_ID hit_component_id on a NO_HIT refusal, distinct from a NO_OWNER refusal which still reports it")
val scene = _l9_button_scene(5u32, 0u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = [_l9_owner(5u32, 0u32, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID)]
val receipt = ui_scene_route_event(scene, resolved, owners, 500, 500)
expect(receipt.hit_component_id).to_equal(DRAW_IR_V3_NO_ID)
```

</details>

### ui_scene_route_event hidden-group hit exclusion (design section 4.1, gate d)

#### routes to the visible panel beneath a hidden group, not the hidden button inside it

- routes to the visible panel beneath a hidden group, not the hidden button inside it
   - Expected: receipt.accepted is true
   - Expected: receipt.hit_component_id equals `10u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes to the visible panel beneath a hidden group, not the hidden button inside it")
var scene = draw_ir_v3_empty_scene(1u32, 1u32)
scene.hit_shapes = draw_ir_v3_hit_shape_append(scene.hit_shapes, 0, 0, 20, 20, DRAW_IR_V3_HIT_RECT, 0u16, 10u32)
scene.hit_shapes = draw_ir_v3_hit_shape_append(scene.hit_shapes, 0, 0, 20, 20, DRAW_IR_V3_HIT_RECT, 0u16, 21u32)

var panel = draw_ir_v3_empty_command()
panel.kind = DRAW_IR_V3_KIND_RECT
panel.component_id = 10u32
panel.hit_shape_id = 0u32
scene = draw_ir_v3_scene_push_command(scene, panel)

var group = draw_ir_v3_empty_command()
group.kind = DRAW_IR_V3_KIND_GROUP
group.component_id = 20u32
group.flags = DRAW_IR_V3_FLAG_HIDDEN
scene = draw_ir_v3_scene_push_command(scene, group)

var hidden_button = draw_ir_v3_empty_command()
hidden_button.kind = DRAW_IR_V3_KIND_RECT
hidden_button.component_id = 21u32
hidden_button.parent_id = 20u32
hidden_button.hit_shape_id = 1u32
scene = draw_ir_v3_scene_push_command(scene, hidden_button)

val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = [
    _l9_owner(10u32, 0u32, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID),
    _l9_owner(21u32, 0u32, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID)
]
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(true)
expect(receipt.hit_component_id).to_equal(10u32)
print "l9_route_hidden_group hit={receipt.hit_component_id}"
```

</details>

### ui_scene_route_event nested WebView chain (design section 4.1/research section 7, gate c)

#### walks the full nested chain in target-to-root order and stops at the reverse-topmost stacked command

- walks the full nested chain in target-to-root order and stops at the reverse-topmost stacked command
   - Expected: receipt.accepted is true
   - Expected: receipt.hit_component_id equals `100u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("walks the full nested chain in target-to-root order and stops at the reverse-topmost stacked command")
val scene = _l9_stacked_scene(999u32, 100u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = _l9_webview_chain_owners()
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(true)
expect(receipt.hit_component_id).to_equal(100u32)
_l9_expect_chain(receipt.owner_chain, [0u32, 1u32, 2u32, 3u32, 4u32])
print "l9_route_webview_chain hit={receipt.hit_component_id} chain_len={receipt.owner_chain.len()}"
```

</details>

#### bubbles past every GUI/Web ancestor with no action to the WM root's action (window-chrome close never mutates WindowManager directly)

- bubbles past every GUI/Web ancestor with no action to the WM root's action (window-chrome close never mutates WindowManager directly)
   - Expected: receipt.accepted is true
   - Expected: receipt.action_owner_id equals `4u32`
   - Expected: receipt.action_binding_id equals `7u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bubbles past every GUI/Web ancestor with no action to the WM root's action (window-chrome close never mutates WindowManager directly)")
val scene = _l9_stacked_scene(999u32, 100u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = _l9_webview_chain_owners()
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(true)
expect(receipt.action_owner_id).to_equal(4u32)
expect(receipt.action_binding_id).to_equal(7u32)
print "l9_route_bubble_to_wm action_owner={receipt.action_owner_id} action_binding={receipt.action_binding_id}"
```

</details>

#### reports NO_ID action when no owner anywhere in the chain carries one

- reports NO_ID action when no owner anywhere in the chain carries one
   - Expected: receipt.accepted is true
   - Expected: receipt.action_owner_id equals `DRAW_IR_V3_NO_ID`
   - Expected: receipt.action_binding_id equals `DRAW_IR_V3_NO_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports NO_ID action when no owner anywhere in the chain carries one")
val scene = _l9_stacked_scene(999u32, 100u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = [
    _l9_owner(100u32, 0u32, 1u32, DRAW_IR_V3_NO_ID),
    _l9_owner(101u32, 0u32, DRAW_IR_V3_NO_ID, DRAW_IR_V3_NO_ID)
]
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(true)
expect(receipt.action_owner_id).to_equal(DRAW_IR_V3_NO_ID)
expect(receipt.action_binding_id).to_equal(DRAW_IR_V3_NO_ID)
```

</details>

#### stops at the NEAREST ancestor action, not a farther one, when both carry one

- stops at the NEAREST ancestor action, not a farther one, when both carry one
   - Expected: receipt.accepted is true
   - Expected: receipt.action_owner_id equals `0u32`
   - Expected: receipt.action_binding_id equals `42u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stops at the NEAREST ancestor action, not a farther one, when both carry one")
val owners = [
    _l9_owner(100u32, 0u32, 1u32, 42u32),      # target itself carries an action
    _l9_owner(101u32, 0u32, DRAW_IR_V3_NO_ID, 99u32)  # parent also carries one -- must not win
]
val scene = _l9_stacked_scene(999u32, 100u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(true)
expect(receipt.action_owner_id).to_equal(0u32)
expect(receipt.action_binding_id).to_equal(42u32)
```

</details>

### ui_scene_route_event composes with menu-action dispatch validation

#### hands the resolved action_binding_id to ui_scene_validate_menu_action_dispatch for a live app generation

- hands the resolved action_binding_id to ui_scene_validate_menu_action_dispatch for a live app generation
   - Expected: receipt.accepted is true
   - Expected: verdict.accepted is true
   - Expected: verdict.reason equals `UI_SCENE_DISPATCH_OK`
   - Expected: verdict.target_owner_id equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hands the resolved action_binding_id to ui_scene_validate_menu_action_dispatch for a live app generation")
val scene = _l9_stacked_scene(999u32, 100u32)
val resolved = draw_ir_v3_group_resolve(scene, draw_ir_v3_port_surface_state_empty())
val owners = _l9_webview_chain_owners()
val receipt = ui_scene_route_event(scene, resolved, owners, 5, 5)
expect(receipt.accepted).to_equal(true)

val binding = MenuActionBinding(app_id: 1u32, app_generation: 3u32, menu_revision: 2u32, action_id: receipt.action_binding_id, default_target_owner_id: 4u32)
val verdict = ui_scene_validate_menu_action_dispatch(binding, 3u32, 2u32)
expect(verdict.accepted).to_equal(true)
expect(verdict.reason).to_equal(UI_SCENE_DISPATCH_OK)
expect(verdict.target_owner_id).to_equal(4u32)
print "l9_route_dispatch_compose action_binding={receipt.action_binding_id} target={verdict.target_owner_id}"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/ui_scene_event_route_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ui_scene_route_event component identity (design section 9, gate a), ui_scene_route_event stale generation (design section 9, gate b), ui_scene_route_event no-hit and no-owner refusals, ui_scene_route_event hidden-group hit exclusion (design section 4.1, gate d), ui_scene_route_event nested WebView chain (design section 4.1/research section 7, gate c), ui_scene_route_event composes with menu-action dispatch validation.
- ui_scene_route_event component identity (design section 9, gate a)
- ui_scene_route_event stale generation (design section 9, gate b)
- ui_scene_route_event no-hit and no-owner refusals
- ui_scene_route_event hidden-group hit exclusion (design section 4.1, gate d)
- ui_scene_route_event nested WebView chain (design section 4.1/research section 7, gate c)
- ui_scene_route_event composes with menu-action dispatch validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d25999bcb66f35f752cc919774d7ecc11a9abbc50ba713915f9568448f51bac8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d25999bcb66f35f752cc919774d7ecc11a9abbc50ba713915f9568448f51bac8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d25999bcb66f35f752cc919774d7ecc11a9abbc50ba713915f9568448f51bac8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/ui/ui_scene_event_route_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/ui_scene_event_route_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/ui_scene_event_route_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/ui_scene_event_route_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/ui_scene_event_route_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/ui_scene_event_route_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a hit to the exact component_id shared by the command, its hit shape and its owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_event_route_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a hit whose command generation no longer matches the owner table's current generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_scene_event_route_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delivers an empty owner chain and NO_ID action on a stale-generation refusal (never a partial delivery)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
