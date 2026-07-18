# Window Winit Wrapper Specification

> <details>

<!-- sdn-diagram:id=window_winit_wrapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_winit_wrapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_winit_wrapper_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_winit_wrapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Winit Wrapper Specification

## Scenarios

### window_winit safety guards

#### invalid event loop

#### yields an invalid window without touching the runtime

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# An invalid loop must NOT call rt_winit_window_new (which is absent
# from the test binary) — the guard returns an invalid window first.
val lp = WinitLoop(handle: 0, is_valid: false)
val win = winit_window_new(lp, 96, 72, "guard")
expect(win.is_valid).to_equal(false)
expect(win.handle).to_equal(0)
```

</details>

<details>
<summary>Advanced: polls to false without entering the drain loop</summary>

#### polls to false without entering the drain loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The early-out (`if not lp.is_valid: return false`) means no event is
# ever polled, so there is no event to leak — and no extern is called.
val lp = WinitLoop(handle: 0, is_valid: false)
expect(winit_poll_close_requested(lp)).to_equal(false)
```

</details>


</details>

#### invalid window

#### present is a no-op (guard prevents the extern call)

1. winit present rgba
   - Expected: win.is_valid is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val win = WinitWindow(handle: 0, is_valid: false)
val pixels: [i64] = [0, 0, 0, 0]
winit_present_rgba(win, 2, 2, pixels)
# Reaching here without a missing-extern abort proves the guard held.
expect(win.is_valid).to_equal(false)
```

</details>

#### free on invalid handles

<details>
<summary>Advanced: loop and window free are no-ops on invalid handles</summary>

#### loop and window free are no-ops on invalid handles

1. winit loop free

2. winit window free
   - Expected: lp.is_valid is false
   - Expected: win.is_valid is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lp = WinitLoop(handle: 0, is_valid: false)
val win = WinitWindow(handle: 0, is_valid: false)
winit_loop_free(lp)
winit_window_free(win)
expect(lp.is_valid).to_equal(false)
expect(win.is_valid).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/window_winit_wrapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- window_winit safety guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
