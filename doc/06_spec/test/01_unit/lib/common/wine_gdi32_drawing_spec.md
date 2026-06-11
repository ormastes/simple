# Wine Gdi32 Drawing Specification

> <details>

<!-- sdn-diagram:id=wine_gdi32_drawing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_gdi32_drawing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_gdi32_drawing_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_gdi32_drawing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Gdi32 Drawing Specification

## Scenarios

### Wine GDI32 drawing bridge

#### executes a bounded text blit through GDI32 drawing calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_gdi32_execute_text_blit(["CreateCompatibleDC", "TextOutW", "BitBlt", "DeleteDC"], 77, "Hello from GDI", 320, 200)
expect(result.ok).to_equal(true)
expect(result.hdc).to_equal(77)
expect(result.text).to_equal("Hello from GDI")
expect(result.operations).to_contain("CreateCompatibleDC")
expect(result.operations).to_contain("TextOutW")
expect(result.operations).to_contain("BitBlt")
expect(result.operations).to_contain("DeleteDC")
expect(result.checksum).to_be_greater_than(0)
```

</details>

#### keeps GDI32 drawing dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_gdi32_execute_text_blit(["TextOutW", "CreateCompatibleDC", "BitBlt", "DeleteDC"], 77, "Hello", 320, 200)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("gdi32-sequence-expected:CreateCompatibleDC")

val unsupported = wine_gdi32_execute_text_blit(["CreateCompatibleDC", "TextOutW", "GetMessageW", "DeleteDC"], 77, "Hello", 320, 200)
expect(unsupported.ok).to_equal(false)
expect(unsupported.error).to_equal("bridge-unsupported:GetMessageW")

val invalid = wine_gdi32_execute_text_blit(["CreateCompatibleDC", "TextOutW", "BitBlt", "DeleteDC"], 0, "Hello", 320, 200)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("invalid-hdc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_gdi32_drawing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine GDI32 drawing bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
