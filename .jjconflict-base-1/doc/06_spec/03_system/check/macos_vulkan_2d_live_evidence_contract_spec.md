# Macos Vulkan 2d Live Evidence Contract Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Vulkan 2d Live Evidence Contract Specification

## Scenarios

### macOS Vulkan 2D live evidence

#### launch backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
expect(source).to_contain("SIMPLE_GUI_BACKEND=vulkan")
expect(source).to_contain("SHOWCASE_RESOLUTION=\"$REQUESTED_RESOLUTION\"")
expect(source).to_contain("SHOWCASE_DPI=\"$REQUESTED_DPI\"")
```

</details>

#### render deterministic scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
expect(source).to_contain("renderer-dimensions-mismatch")
expect(source).to_contain("renderer-dpi-mismatch")
expect(source).to_contain("vector-font-warm-cache-hit-missing")
```

</details>

#### deliver input events

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
expect(source).to_contain("focus,pointer_move,pointer_down,pointer_up,key_down,key_up")
expect(source).to_contain("event-count-mismatch")
expect(source).to_contain("event-backend-mismatch")
```

</details>

#### capture framebuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
expect(source).to_contain("durable-capture-hash-mismatch")
expect(source).to_contain("durable-capture-not-ppm")
expect(source).to_contain("non-background-bounds-missing")
```

</details>

#### compare evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read(WRAPPER)
for field in [
    "backend", "target", "width", "height", "dpi", "pixel_sha256",
    "non_background_bounds", "event_sequence", "event_count",
    "event_backend", "capture_path", "source_revision"
]:
    expect(source).to_contain("echo \"{field}=")
expect(source).to_contain("spirv-val --target-env vulkan1.1")
expect(source).to_contain("event-source-receipt-mismatch")
expect(source).to_contain("event-handle-receipt-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/macos_vulkan_2d_live_evidence_contract_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- macOS Vulkan 2D live evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
