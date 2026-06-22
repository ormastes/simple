# Hosted Backend Cocoa Specification

> <details>

<!-- sdn-diagram:id=hosted_backend_cocoa_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hosted_backend_cocoa_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hosted_backend_cocoa_spec -> std
hosted_backend_cocoa_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hosted_backend_cocoa_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Backend Cocoa Specification

## Scenarios

### HostedCocoaBackend native boundary

#### names the implementation as the Cocoa SFFI backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(HostedCocoaBackend.implementation_name()).to_equal("cocoa-real-sffi")
```

</details>

#### documents that native Cocoa symbols are bound by this class

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(HostedCocoaBackend.uses_native_cocoa_symbols()).to_equal(true)
```

</details>

#### instantiates through the test seam without touching SFFI

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = HostedCocoaBackend.new(11, 22, 320, 240)
expect(be.window_id).to_equal(11)
expect(be.buffer_id).to_equal(22)
expect(be.w).to_equal(320)
expect(be.h).to_equal(240)
```

</details>

#### keeps CompositorBackend method signatures aligned with u32/i32 contract

1. be clear
2. be fill rect
3. be draw text
4. be draw char 8x16
5. be put pixel
6. be present
7. be present rect
   - Expected: be.w equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = HostedCocoaBackend.new(0, 0, 128, 128)
if false:
    be.clear(0xFF000000)
    be.fill_rect(0, 0, 10, 10, 0xFFFFFFFF)
    be.draw_text(0, 0, "x", 0xFFFFFFFF, 0xFF000000)
    val ch: u8 = 65
    be.draw_char_8x16(0, 0, ch, 0xFFFFFFFF, 0xFF000000)
    be.put_pixel(0, 0, 0xFF0000FF)
    be.present()
    be.present_rect(0, 0, 64, 64)
expect(be.w).to_equal(128)
```

</details>

#### keeps glass method signatures aligned with u32/i32 contract

1. be blend rect
2. be blur region
3. be gradient v
   - Expected: be.h equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = HostedCocoaBackend.new(0, 0, 128, 128)
if false:
    val alpha: u8 = 128
    be.blend_rect(0, 0, 64, 64, 0x80FFFFFF, alpha)
    val radius: u32 = 4
    be.blur_region(0, 0, 64, 64, radius)
    be.gradient_v(0, 0, 64, 64, 0xFF000000, 0xFFFFFFFF)
    val _px = be.read_pixel(0, 0)
expect(be.h).to_equal(128)
```

</details>

#### keeps lifecycle signatures deterministic

1. be free
   - Expected: be.w + be.h equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val be = HostedCocoaBackend.new(0, 0, 64, 64)
if false:
    val _created = HostedCocoaBackend.try_create(1, 64, 64, 0xFF000000)
    val _ok = be.resize(128, 128)
    be.free()
expect(be.w + be.h).to_equal(128)
```

</details>

#### rejects invalid native Cocoa surface sizes before SFFI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = HostedCocoaBackend.try_create(0, 0, 64, 0xFF000000)
expect(created == nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/hosted_backend_cocoa_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HostedCocoaBackend native boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
