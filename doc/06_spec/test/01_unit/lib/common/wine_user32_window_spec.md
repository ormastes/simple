# Wine User32 Window Specification

> <details>

<!-- sdn-diagram:id=wine_user32_window_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_user32_window_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_user32_window_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_user32_window_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine User32 Window Specification

## Scenarios

### Wine USER32 window lifecycle bridge

#### executes CreateWindowExW, ShowWindow, UpdateWindow, and DefWindowProcW through SimpleOS records

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_user32_execute_window_lifecycle(["CreateWindowExW", "ShowWindow", "UpdateWindow", "DefWindowProcW"], 4001, "SimpleOS USER32 Window", 320, 200, 7)
expect(result.ok).to_equal(true)
expect(result.hwnd).to_equal(4001)
expect(result.title).to_equal("SimpleOS USER32 Window")
expect(result.operations).to_contain("create")
expect(result.operations).to_contain("map")
expect(result.operations).to_contain("simpleos-framebuffer-present")
expect(result.operations).to_contain("destroy")
expect(result.checksum).to_be_greater_than(0)
```

</details>

#### keeps lifecycle dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = wine_user32_execute_window_lifecycle(["CreateWindowExW", "ShowWindow", "UpdateWindow"], 4001, "title", 320, 200, 7)
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("user32-sequence-count-mismatch")

val out_of_order = wine_user32_execute_window_lifecycle(["ShowWindow", "CreateWindowExW", "UpdateWindow", "DefWindowProcW"], 4001, "title", 320, 200, 7)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("user32-sequence-expected:CreateWindowExW")

val unsupported = wine_user32_execute_window_lifecycle(["CreateWindowExW", "GetMessageW", "UpdateWindow", "DefWindowProcW"], 4001, "title", 320, 200, 7)
expect(unsupported.ok).to_equal(false)
expect(unsupported.error).to_equal("user32-sequence-expected:ShowWindow")
```

</details>

<details>
<summary>Advanced: executes a bounded USER32 message loop for a created window</summary>

#### executes a bounded USER32 message loop for a created window

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_user32_execute_message_loop(["PeekMessageW", "GetMessageW", "TranslateMessage", "DispatchMessageW"], 4001, "WM_PAINT")
expect(result.ok).to_equal(true)
expect(result.hwnd).to_equal(4001)
expect(result.message).to_equal("WM_PAINT")
expect(result.translated).to_equal(true)
expect(result.dispatched_count).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: keeps message loop dispatch ordered and bounded</summary>

#### keeps message loop dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_user32_execute_message_loop(["GetMessageW", "PeekMessageW", "TranslateMessage", "DispatchMessageW"], 4001, "WM_PAINT")
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("user32-message-sequence-expected:PeekMessageW")

val unsupported = wine_user32_execute_message_loop(["PeekMessageW", "GetMessageW", "TextOutW", "DispatchMessageW"], 4001, "WM_PAINT")
expect(unsupported.ok).to_equal(false)
expect(unsupported.error).to_equal("bridge-unsupported:TextOutW")

val invalid = wine_user32_execute_message_loop(["PeekMessageW", "GetMessageW", "TranslateMessage", "DispatchMessageW"], 0, "WM_PAINT")
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("invalid-hwnd")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_user32_window_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine USER32 window lifecycle bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
