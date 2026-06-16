# counter_route_spec

> This spec pins the production Office contract for the requested counter interaction. The current LibreOffice-style office suite has no `counter` component; an attempted `counter` command or `open_counter` launcher action must fail closed instead of silently routing to another Office surface.

<!-- sdn-diagram:id=counter_route_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=counter_route_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

counter_route_spec -> std
counter_route_spec -> app
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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# counter_route_spec

This spec pins the production Office contract for the requested counter interaction. The current LibreOffice-style office suite has no `counter` component; an attempted `counter` command or `open_counter` launcher action must fail closed instead of silently routing to another Office surface.

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
interaction. The current LibreOffice-style office suite has no `counter`
component; an attempted `counter` command or `open_counter` launcher action must
fail closed instead of silently routing to another Office surface.

## Syntax

The scenario exercises the CLI dispatcher, launcher action parser, and
LibreOffice component resolver with counter-shaped inputs.

**Requirements:** N/A
**Research:** N/A
**Plan:** N/A
**Design:** N/A

Tracked by `.spipe/ide_md_counter_office_hardening/state.md` AC-3. No
production Office counter component exists in current source, so this spec
validates the fail-closed interaction contract.

## Scenarios

### Office counter route hardening
_Counter-shaped user interactions are rejected before Office dispatch._

#### rejects counter CLI command without falling back to another app

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(run_office(["counter"])).to_equal(1)
```

</details>

#### rejects open_counter launcher action before component dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_valid_launcher_action("open_counter")).to_be(false)
val component = launcher_action_to_component("open_counter")
expect(component.is_none()).to_be(true)
```

</details>

#### reports counter as an unsupported LibreOffice component

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = lookup_office_component("counter")
expect(route.valid).to_be(false)
expect(route.status).to_equal("unsupported")
expect(route.component).to_equal("")
expect(libreoffice_app_name_checked("counter")).to_equal("error: unknown LibreOffice component: counter")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
