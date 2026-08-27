# Wm App Process Contract Specification

> <details>

<!-- sdn-diagram:id=wm_app_process_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_app_process_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_app_process_contract_spec -> std
wm_app_process_contract_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_app_process_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm App Process Contract Specification

## Scenarios

### WM app process contract

#### names the widget showcase source file as the executable app identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WIDGET_SHOWCASE_APP_SOURCE).to_equal("examples/06_io/ui/widget_showcase_metal_gui.spl")
expect(WIDGET_SHOWCASE_APP_ID).to_equal("/examples/widget-showcase")
expect(WIDGET_SHOWCASE_TITLE).to_equal("Widget Showcase")
```

</details>

#### distinguishes native launch from WM client launch by mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wm_app_mode_is_client(WM_APP_MODE_CLIENT)).to_equal(true)
expect(wm_app_mode_is_client("")).to_equal(false)
expect(wm_app_mode_is_client("native")).to_equal(false)
```

</details>

#### round-trips the filesystem child bridge request

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = wm_widget_showcase_bridge_request(1234, "build/tmp/showcase.ppm")
val encoded = wm_fs_bridge_encode(req)
val decoded = wm_fs_bridge_decode(encoded)
expect(decoded.kind).to_equal("create_window")
expect(decoded.source_path).to_equal(WIDGET_SHOWCASE_APP_SOURCE)
expect(decoded.app_id).to_equal(WIDGET_SHOWCASE_APP_ID)
expect(decoded.title).to_equal(WIDGET_SHOWCASE_TITLE)
expect(decoded.pid).to_equal(1234)
expect(decoded.frame_path).to_equal("build/tmp/showcase.ppm")
expect(decoded.event_path).to_equal("build/tmp/showcase.ppm.event")
expect(decoded.frame_seq_path).to_equal("build/tmp/showcase.ppm.seq")
expect(decoded.content).to_contain(WIDGET_SHOWCASE_APP_SOURCE)
```

</details>

#### builds the child environment used by host and simple-os launchers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env = wm_widget_showcase_client_env("bridge.sdn", "frame.ppm")
expect(env[WM_APP_MODE_ENV]).to_equal(WM_APP_MODE_CLIENT)
expect(env[WM_BRIDGE_FILE_ENV]).to_equal("bridge.sdn")
expect(env[WM_FRAME_FILE_ENV]).to_equal("frame.ppm")
expect(env[WM_EVENT_FILE_ENV]).to_equal("frame.ppm.event")
expect(env[WM_FRAME_SEQ_FILE_ENV]).to_equal("frame.ppm.seq")
expect(env[WM_CLIENT_HOLD_ENV]).to_equal("1")
```

</details>

#### declares child-content pointer input on the shared filesystem bridge

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = wm_fs_app_event(7, "down", 32, 44, 0, true)
val decoded = wm_fs_app_event_decode(wm_fs_app_event_encode(ev))
expect(decoded.seq).to_equal(7)
expect(decoded.kind).to_equal("down")
expect(decoded.x).to_equal(32)
expect(decoded.y).to_equal(44)
expect(decoded.button).to_equal(0)
expect(decoded.pressed).to_equal(true)
```

</details>

#### tracks child frame sequence updates through the bridge request

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = wm_widget_showcase_bridge_request(5, "child.ppm")
expect(req.event_path).to_equal(wm_widget_showcase_event_path("child.ppm"))
expect(req.frame_seq_path).to_equal(wm_widget_showcase_frame_seq_path("child.ppm"))
val decoded = wm_fs_bridge_decode(wm_fs_bridge_encode(req))
expect(decoded.event_path).to_equal("child.ppm.event")
expect(decoded.frame_seq_path).to_equal("child.ppm.seq")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wm_app_process_contract_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WM app process contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
