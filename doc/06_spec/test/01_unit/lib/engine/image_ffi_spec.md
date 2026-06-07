# image_ffi_spec

> Engine ImageData Tests

<!-- sdn-diagram:id=image_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=image_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

image_ffi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=image_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# image_ffi_spec

Engine ImageData Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/image_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine ImageData Tests

Tests ImageData struct construction, validity, pixel_count, and size_bytes.
Does not test FFI extern functions (those require runtime).

## Scenarios

### ImageData

### create_image_data

#### creates with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = create_image_data(32, 16, [])
expect(img.width).to_equal(32)
expect(img.height).to_equal(16)
```

</details>

#### defaults to 4 channels (RGBA)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = create_image_data(8, 8, [])
expect(img.channels).to_equal(4)
```

</details>

#### stores pixel data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels: [i64] = [255, 0, 128, 64]
val img = create_image_data(2, 2, pixels)
expect(img.pixels.len()).to_equal(4)
```

</details>

### is_valid

#### returns true for positive dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = create_image_data(10, 20, [])
expect(img.is_valid()).to_equal(true)
```

</details>

#### returns false for zero width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = ImageData(width: 0, height: 10, channels: 4, pixels: [])
expect(img.is_valid()).to_equal(false)
```

</details>

#### returns false for zero height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = ImageData(width: 10, height: 0, channels: 4, pixels: [])
expect(img.is_valid()).to_equal(false)
```

</details>

#### returns false for zero width and zero height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = ImageData(width: 0, height: 0, channels: 4, pixels: [])
expect(img.is_valid()).to_equal(false)
```

</details>

### pixel_count

#### returns width times height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = create_image_data(8, 4, [])
expect(img.pixel_count()).to_equal(32)
```

</details>

#### returns zero for zero-dimension image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = ImageData(width: 0, height: 5, channels: 4, pixels: [])
expect(img.pixel_count()).to_equal(0)
```

</details>

### size_bytes

#### returns width times height times channels

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = create_image_data(10, 10, [])
# 10 * 10 * 4 = 400
expect(img.size_bytes()).to_equal(400)
```

</details>

#### respects channel count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = ImageData(width: 4, height: 4, channels: 3, pixels: [])
# 4 * 4 * 3 = 48
expect(img.size_bytes()).to_equal(48)
```

</details>

#### returns zero for invalid image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = ImageData(width: 0, height: 10, channels: 4, pixels: [])
expect(img.size_bytes()).to_equal(0)
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
