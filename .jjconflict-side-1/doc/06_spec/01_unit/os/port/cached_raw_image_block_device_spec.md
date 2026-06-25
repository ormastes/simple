# Cached Raw Image Block Device Specification

> 1.  cleanup

<!-- sdn-diagram:id=cached_raw_image_block_device_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cached_raw_image_block_device_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cached_raw_image_block_device_spec -> std
cached_raw_image_block_device_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cached_raw_image_block_device_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cached Raw Image Block Device Specification

## Scenarios

### CachedRawImageBlockDevice

#### loads a host image and exposes block-device reads

1.  cleanup
   - Expected: rt_dir_create_all(root) is true
2. var image =  repeat byte
   - Expected: rt_file_write_bytes(root + "/disk.img", image) is true
   - Expected: device_result.is_ok() is true
   - Expected: device.image_bytes[512] equals `0x11u8`
   - Expected: device.image_bytes[513] equals `0x22u8`
   - Expected: device.image_bytes[514] equals `0x33u8`
   - Expected: second_result.is_ok() is true
   - Expected: second[0] equals `0x11u8`
   - Expected: second[1] equals `0x22u8`
   - Expected: second[2] equals `0x33u8`
3.  cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/cached_raw_image_block_device_spec_load"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)

var image = _repeat_byte(1024, 0u8)
image[512] = 0x11u8
image[513] = 0x22u8
image[514] = 0x33u8
expect(rt_file_write_bytes(root + "/disk.img", image)).to_equal(true)

val device_result = CachedRawImageBlockDevice.load(root + "/disk.img")
expect(device_result.is_ok()).to_equal(true)
val device = device_result.unwrap()
expect(device.image_bytes[512]).to_equal(0x11u8)
expect(device.image_bytes[513]).to_equal(0x22u8)
expect(device.image_bytes[514]).to_equal(0x33u8)

val second_result = device.read_sector(1u64)
expect(second_result.is_ok()).to_equal(true)
val second = second_result.unwrap()
expect(second[0]).to_equal(0x11u8)
expect(second[1]).to_equal(0x22u8)
expect(second[2]).to_equal(0x33u8)

_cleanup(root)
```

</details>

#### reads writes and flushes sectors for a preloaded in-memory image

1.  cleanup
   - Expected: rt_dir_create_all(root) is true
   - Expected: rt_file_write_bytes(path, _repeat_byte(1024, 0u8)) is true
   - Expected: device_result.is_ok() is true
2. var device = device result unwrap
   - Expected: device.write_sector(1u64, [0xAAu8, 0xBBu8, 0xCCu8]).is_ok() is true
   - Expected: device.dirty is true
   - Expected: second_result.is_ok() is true
   - Expected: second[0] equals `0xAAu8`
   - Expected: second[1] equals `0xBBu8`
   - Expected: second[2] equals `0xCCu8`
   - Expected: second[3] equals `0u8`
   - Expected: device.flush().is_ok() is true
   - Expected: device.dirty is false
   - Expected: reloaded_result.is_ok() is true
   - Expected: reloaded_sector_result.is_ok() is true
   - Expected: reloaded_sector[0] equals `0xAAu8`
   - Expected: reloaded_sector[1] equals `0xBBu8`
   - Expected: reloaded_sector[2] equals `0xCCu8`
3.  cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/cached_raw_image_block_device_spec_write"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)

val path = root + "/disk.img"
expect(rt_file_write_bytes(path, _repeat_byte(1024, 0u8))).to_equal(true)
val device_result = CachedRawImageBlockDevice.from_bytes(path, _repeat_byte(1024, 0u8), 512u32)
expect(device_result.is_ok()).to_equal(true)
var device = device_result.unwrap()

expect(device.write_sector(1u64, [0xAAu8, 0xBBu8, 0xCCu8]).is_ok()).to_equal(true)
expect(device.dirty).to_equal(true)

val second_result = device.read_sector(1u64)
expect(second_result.is_ok()).to_equal(true)
val second = second_result.unwrap()
expect(second[0]).to_equal(0xAAu8)
expect(second[1]).to_equal(0xBBu8)
expect(second[2]).to_equal(0xCCu8)
expect(second[3]).to_equal(0u8)

expect(device.flush().is_ok()).to_equal(true)
expect(device.dirty).to_equal(false)

val reloaded_result = CachedRawImageBlockDevice.load(path)
expect(reloaded_result.is_ok()).to_equal(true)
val reloaded = reloaded_result.unwrap()
val reloaded_sector_result = reloaded.read_sector(1u64)
expect(reloaded_sector_result.is_ok()).to_equal(true)
val reloaded_sector = reloaded_sector_result.unwrap()
expect(reloaded_sector[0]).to_equal(0xAAu8)
expect(reloaded_sector[1]).to_equal(0xBBu8)
expect(reloaded_sector[2]).to_equal(0xCCu8)

_cleanup(root)
```

</details>

#### rejects host images whose byte length is not sector aligned

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = CachedRawImageBlockDevice.from_bytes("", [1u8, 2u8, 3u8], 512u32)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/cached_raw_image_block_device_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CachedRawImageBlockDevice

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
