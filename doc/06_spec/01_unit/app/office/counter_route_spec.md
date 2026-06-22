# counter_route_spec

> This spec pins the production Office contract for the requested counter interaction. `counter` is a small Office entrypoint with deterministic state transitions, and counter-shaped launcher actions must resolve to that component instead of silently routing to another Office surface.

<!-- sdn-diagram:id=counter_route_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=counter_route_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

counter_route_spec -> std
counter_route_spec -> app
counter_route_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=counter_route_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# counter_route_spec

This spec pins the production Office contract for the requested counter interaction. `counter` is a small Office entrypoint with deterministic state transitions, and counter-shaped launcher actions must resolve to that component instead of silently routing to another Office surface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/office/counter_route_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec pins the production Office contract for the requested counter
interaction. `counter` is a small Office entrypoint with deterministic state
transitions, and counter-shaped launcher actions must resolve to that component
instead of silently routing to another Office surface.

## Syntax

The scenario exercises the CLI dispatcher, launcher action parser, and
LibreOffice component resolver with counter-shaped inputs.

**Requirements:** N/A
**Research:** N/A
**Plan:** N/A
**Design:** N/A

Tracked by `.spipe/ide_md_counter_office_hardening/state.md` AC-3.

## Scenarios

### Office counter route hardening
_Counter-shaped user interactions route to deterministic counter state._

#### loads counter CLI command without falling back to another app

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["counter"])).to_equal(0)
```

</details>

#### resolves open_counter launcher action before component dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_launcher_action("open_counter")).to_be(true)
val component = launcher_action_to_component("open_counter")
expect(component.is_some()).to_be(true)
expect(component.unwrap()).to_equal("counter")
```

</details>

#### reports counter as a supported Office component

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = lookup_office_component("counter")
expect(route.valid).to_be(true)
expect(route.status).to_equal("component")
expect(route.component).to_equal("counter")
expect(libreoffice_app_name_checked("counter")).to_equal("Counter")
```

</details>

#### applies deterministic counter state transitions and fails closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inc = counter_apply_action(0, "counter_increment")
expect(inc.value).to_equal(1)
expect(inc.status).to_equal("incremented")
expect(inc.changed).to_be(true)

val dec = counter_apply_action(inc.value, "counter_decrement")
expect(dec.value).to_equal(0)
expect(dec.status).to_equal("decremented")
expect(dec.changed).to_be(true)

val invalid = counter_apply_action(dec.value, "counter_delete_everything")
expect(invalid.value).to_equal(0)
expect(invalid.status).to_equal("unsupported")
expect(invalid.changed).to_be(false)
```

</details>

#### updates CounterApp through UI actions

- var app = CounterApp new
   - Expected: ui.root_id equals `root`
- app handle event
   - Expected: app.value equals `1`
- app handle event
   - Expected: app.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = CounterApp.new()
val ui = app.build_ui()
expect(ui.root_id).to_equal("root")
app.handle_event(UIEvent.Action(name: "counter_increment"))
expect(app.value).to_equal(1)
expect(app.modified).to_be(true)
app.handle_event(UIEvent.Action(name: "counter_reset"))
expect(app.value).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
