# Smux Api Specification

> 1. smux reset for test

<!-- sdn-diagram:id=smux_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smux_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smux_api_spec -> std
smux_api_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smux_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smux Api Specification

## Scenarios

### smux api

#### creates a session with an initial pane

1. smux reset for test
   - Expected: windows.len() equals `1`
   - Expected: panes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("dev")
val windows = smux_list_windows(session.id)
val panes = smux_list_panes(session.id, windows[0].id)

expect(windows.len()).to_equal(1)
expect(panes.len()).to_equal(1)
```

</details>

#### splits a pane and captures buffered output

1. smux reset for test
   - Expected: smux_split_pane(session.id, window.id, pane.id, "vertical").is_ok() is true
   - Expected: panes.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("split")
val window = smux_list_windows(session.id)[0]
val pane = smux_list_panes(session.id, window.id)[0]

expect(smux_split_pane(session.id, window.id, pane.id, "vertical").is_ok()).to_equal(true)
val panes = smux_list_panes(session.id, window.id)
expect(panes.len()).to_equal(2)

val capture = smux_capture(session.id, window.id, panes[0].id, 20)
expect(capture.rows).to_be_greater_than(0)
```

</details>

#### tracks attach and detach

1. smux reset for test
   - Expected: smux_attach(session.id, "client-a", 100, 30).attached is true
   - Expected: smux_detach("client-a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("attach")
expect(smux_attach(session.id, "client-a", 100, 30).attached).to_equal(true)
expect(smux_detach("client-a")).to_equal(true)
```

</details>

#### records observable metrics and applies resize

1. smux reset for test
   - Expected: smux_resize(session.id, window.id, pane.id, 120, 40).is_ok() is true
   - Expected: metrics.resize_count equals `1`
   - Expected: metrics.capture_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
smux_reset_for_test()
val session = smux_create_session("metrics")
val window = smux_list_windows(session.id)[0]
val pane = smux_list_panes(session.id, window.id)[0]

expect(smux_resize(session.id, window.id, pane.id, 120, 40).is_ok()).to_equal(true)
expect(smux_capture(session.id, window.id, pane.id, 20).rows).to_be_greater_than(0)

val metrics = smux_metrics()
expect(metrics.startup_count).to_be_greater_than(0)
expect(metrics.resize_count).to_equal(1)
expect(metrics.capture_count).to_equal(1)
```

</details>

#### exposes deferred parity features explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(smux_is_deferred_feature("copy-mode")).to_equal(true)
expect(smux_is_deferred_feature("mouse")).to_equal(true)
expect(smux_is_deferred_feature("split-pane")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/smux/smux_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- smux api

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
