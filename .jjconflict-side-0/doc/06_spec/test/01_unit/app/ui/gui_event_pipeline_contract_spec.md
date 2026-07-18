# Gui Event Pipeline Contract Specification

> <details>

<!-- sdn-diagram:id=gui_event_pipeline_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_event_pipeline_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_event_pipeline_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_event_pipeline_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gui Event Pipeline Contract Specification

## Scenarios

### GUI IPC event pipeline contract

#### keeps webview id aliases wired into focus and input IPC parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/ui.ipc/protocol.spl")
expect(src.contains("tid = extract_json_field(json_str, \"id\")")).to_equal(true)
expect(src.contains("return UIEvent.FocusEvent(target_id: tid, kind: kind)")).to_equal(true)
expect(src.contains("return UIEvent.InputChange(target_id: tid, value: val_str)")).to_equal(true)
```

</details>

#### keeps GUI pointer, focus, input, and fetch events in state processing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/common/ui/event.spl")
expect(src.contains("UIEvent.MouseEvent(x, y, button, kind):")).to_equal(true)
expect(src.contains("UIEvent.ScrollEvent(x, y, dx, dy):")).to_equal(true)
expect(src.contains("UIEvent.FocusEvent(target_id, kind):")).to_equal(true)
expect(src.contains("UIEvent.InputChange(target_id, value):")).to_equal(true)
expect(src.contains("UIEvent.FetchResult(request_id, url, status, headers, body, error):")).to_equal(true)
```

</details>

#### keeps GUI events recorded by UI session dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_sync_mut/ui/session.spl")
expect(src.contains("event_kind = \"mouse_\" + kind")).to_equal(true)
expect(src.contains("event_kind = \"scroll\"")).to_equal(true)
expect(src.contains("event_kind = \"focus_\" + kind")).to_equal(true)
expect(src.contains("event_kind = \"input_change\"")).to_equal(true)
expect(src.contains("event_kind = \"fetch_result\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/gui_event_pipeline_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GUI IPC event pipeline contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
