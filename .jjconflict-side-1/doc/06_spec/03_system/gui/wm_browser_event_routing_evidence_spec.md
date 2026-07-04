# Wm Browser Event Routing Evidence Specification

> <details>

<!-- sdn-diagram:id=wm_browser_event_routing_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_browser_event_routing_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_browser_event_routing_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_browser_event_routing_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Browser Event Routing Evidence Specification

## Scenarios

### WM browser event routing evidence

#### runs the Electron WM probe and records event routing without pixel tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_checker(run_id)
if result[2] != 0:
    print "[wm_browser_event_routing_evidence_spec] stdout:\n{result[0]}"
    print "[wm_browser_event_routing_evidence_spec] stderr:\n{result[1]}"

expect(result[2]).to_equal(0)
expect(result[0]).to_contain("wm_browser_event_routing_status=pass")
expect(result[0]).to_contain("wm_browser_event_routing_reason=pass")
expect(result[0]).to_contain("wm_browser_event_routing_wm_found=true")
expect(result[0]).to_contain("wm_browser_event_routing_blur_or_tolerance_used=false")

val report = rt_file_read_text(_report_path(run_id)) ?? ""
expect(report).to_contain("- status: pass")
expect(report).to_contain("- reason: pass")
expect(report).to_contain("- blur/tolerance used: false")
```

</details>

#### requires titlebar drag maximize command and title command routing

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_checker(run_id)
if result[2] != 0:
    print "[wm_browser_event_routing_evidence_spec] stdout:\n{result[0]}"
    print "[wm_browser_event_routing_evidence_spec] stderr:\n{result[1]}"

expect(result[2]).to_equal(0)
expect(result[0]).to_contain("wm_browser_event_routing_window_cmd_count=4")
expect(result[0]).to_contain("wm_browser_event_routing_focus_count=1")
expect(result[0]).to_contain("wm_browser_event_routing_move_count=1")
expect(result[0]).to_contain("wm_browser_event_routing_maximize_count=1")
expect(result[0]).to_contain("wm_browser_event_routing_title_command_count=1")
expect(result[0]).to_contain("wm_browser_event_routing_title_command_text=/tmp/project")
expect(result[0]).to_contain("wm_browser_event_routing_move_payload_source=native_event")
expect(result[0]).to_contain("wm_browser_event_routing_move_payload_window_id_hint=win1")
```

</details>

#### requires titlebar text input traffic button styling and body input events

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_checker(run_id)
if result[2] != 0:
    print "[wm_browser_event_routing_evidence_spec] stdout:\n{result[0]}"
    print "[wm_browser_event_routing_evidence_spec] stderr:\n{result[1]}"

expect(result[2]).to_equal(0)
expect(result[0]).to_contain("wm_browser_event_routing_input_event_count=3")
expect(result[0]).to_contain("wm_browser_event_routing_text_input_count=1")
expect(result[0]).to_contain("wm_browser_event_routing_pointer_down_count=1")
expect(result[0]).to_contain("wm_browser_event_routing_pointer_up_count=1")
expect(result[0]).to_contain("wm_browser_event_routing_text_input_text=Hello Simple")

val report = rt_file_read_text(_report_path(run_id)) ?? ""
expect(report).to_contain("wm_browser_event_routing_title_input_tag=input")
expect(report).to_contain("wm_browser_event_routing_titlebar_display=flex")
expect(report).to_contain("wm_browser_event_routing_titlebar_cursor=grab")
expect(report).to_contain("wm_browser_event_routing_title_input_cursor=text")
expect(report).to_contain("wm_browser_event_routing_close_button_background=rgb(239, 68, 68)")
expect(report).to_contain("wm_browser_event_routing_minimize_button_background=rgb(234, 179, 8)")
expect(report).to_contain("wm_browser_event_routing_maximize_button_background=rgb(34, 197, 94)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_browser_event_routing_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WM browser event routing evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
