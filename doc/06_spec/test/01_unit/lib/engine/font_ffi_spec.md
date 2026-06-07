# font_ffi_spec

> Engine Font FFI Types Tests

<!-- sdn-diagram:id=font_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=font_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

font_ffi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=font_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# font_ffi_spec

Engine Font FFI Types Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/font_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Font FFI Types Tests

Tests FontHandle, GlyphMetrics, and GlyphBitmap struct construction and methods.
Does not test FFI extern functions (those require runtime).

## Scenarios

### FontHandle

#### constructs with handle and path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val font = FontHandle(handle: 42, path: "/fonts/test.ttf")
expect(font.handle).to_equal(42)
expect(font.path).to_equal("/fonts/test.ttf")
```

</details>

#### is_valid returns true for positive handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val font = FontHandle(handle: 1, path: "test.ttf")
expect(font.is_valid()).to_equal(true)
```

</details>

#### is_valid returns false for zero handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val font = FontHandle(handle: 0, path: "test.ttf")
expect(font.is_valid()).to_equal(false)
```

</details>

#### is_valid returns false for negative handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val font = FontHandle(handle: -1, path: "test.ttf")
expect(font.is_valid()).to_equal(false)
```

</details>

### GlyphMetrics

#### constructs with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 12, height: 16, advance: 14, codepoint: 65)
expect(metrics.width).to_equal(12)
expect(metrics.height).to_equal(16)
expect(metrics.advance).to_equal(14)
expect(metrics.codepoint).to_equal(65)
```

</details>

#### stores zero metrics

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 0, height: 0, advance: 0, codepoint: 32)
expect(metrics.width).to_equal(0)
expect(metrics.height).to_equal(0)
expect(metrics.codepoint).to_equal(32)
```

</details>

### GlyphBitmap

#### constructs with dimensions, bitmap handle, and metrics

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 8, height: 10, advance: 9, codepoint: 65)
val bitmap = GlyphBitmap(bitmap_handle: 99, width: 8, height: 10, metrics: metrics)
expect(bitmap.bitmap_handle).to_equal(99)
expect(bitmap.width).to_equal(8)
expect(bitmap.height).to_equal(10)
expect(bitmap.metrics.codepoint).to_equal(65)
```

</details>

#### is_valid returns true for positive handle and dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 8, height: 10, advance: 9, codepoint: 65)
val bitmap = GlyphBitmap(bitmap_handle: 99, width: 8, height: 10, metrics: metrics)
expect(bitmap.is_valid()).to_equal(true)
```

</details>

#### is_valid returns false for zero width

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 0, height: 10, advance: 0, codepoint: 32)
val bitmap = GlyphBitmap(bitmap_handle: 99, width: 0, height: 10, metrics: metrics)
expect(bitmap.is_valid()).to_equal(false)
```

</details>

#### is_valid returns false for zero height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 8, height: 0, advance: 9, codepoint: 65)
val bitmap = GlyphBitmap(bitmap_handle: 99, width: 8, height: 0, metrics: metrics)
expect(bitmap.is_valid()).to_equal(false)
```

</details>

#### is_valid returns false for both dimensions zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 0, height: 0, advance: 0, codepoint: 0)
val bitmap = GlyphBitmap(bitmap_handle: 99, width: 0, height: 0, metrics: metrics)
expect(bitmap.is_valid()).to_equal(false)
```

</details>

#### is_valid returns false for non-positive bitmap handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = GlyphMetrics(width: 8, height: 10, advance: 9, codepoint: 65)
val bitmap = GlyphBitmap(bitmap_handle: -1, width: 8, height: 10, metrics: metrics)
expect(bitmap.is_valid()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
