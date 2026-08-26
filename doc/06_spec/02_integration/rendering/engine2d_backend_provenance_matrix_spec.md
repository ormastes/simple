# Engine2D Backend Provenance Matrix Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Backend Provenance Matrix Specification

## Scenarios

### Engine2D backend provenance matrix

#### labels DirectX and Metal requests translated onto Vulkan

The real strict facade creates each compatibility lane inline. If Vulkan is
available, both lanes must retain their explicit translated names, return
device-origin readbacks with positive handles and device identities, and
produce identical pixels and checksums. An unavailable host must return a
nonempty diagnostic instead of silently falling back.

#### keeps native Windows and macOS checkpoints honest on Linux

On Linux, the DirectX request may only report
`directx-software-emulation`; strict Metal must remain unavailable and retain
the requested backend identity. Other hosts retain a nonempty platform name.

#### rejects CPU fallback from a backend-specific pass

An unknown strict backend must return a typed diagnostic whose requested name
is unchanged and whose selected name is not `cpu`.

<details>
<summary>Executable SSpec</summary>

Complete executable scenarios:

```simple
step("Request DirectX and Metal compatibility lanes")
var directx_pixels: [u32] = []
var directx_checksum: i64 = 0
match Engine2D.create_requested_backend(8, 4, "directx-on-vulkan"):
    Err(reason): expect(reason.len()).to_be_greater_than(0)
    Ok(directx):
        expect(directx.backend_name()).to_equal("directx-on-vulkan")
        directx.clear(0xff102030u32)
        directx.draw_rect_filled(2, 1, 4, 2, 0xffa0b0c0u32)
        directx.present()
        val directx_readback = directx.read_pixels_with_source()
        expect(directx_readback.source).to_equal("device_readback")
        expect(directx_readback.backend_handle).to_be_greater_than(0)
        expect(directx_readback.device_identity).to_be_greater_than(0)
        expect(directx_readback.pixel_count).to_equal(32)
        expect(directx_readback.checksum).to_be_greater_than(0)
        directx_pixels = directx_readback.pixels
        directx_checksum = directx_readback.checksum
        directx.shutdown()
match Engine2D.create_requested_backend(8, 4, "metal-on-vulkan"):
    Err(reason): expect(reason.len()).to_be_greater_than(0)
    Ok(metal):
        expect(metal.backend_name()).to_equal("metal-on-vulkan")
        metal.clear(0xff102030u32)
        metal.draw_rect_filled(2, 1, 4, 2, 0xffa0b0c0u32)
        metal.present()
        val metal_readback = metal.read_pixels_with_source()
        expect(metal_readback.source).to_equal("device_readback")
        expect(metal_readback.backend_handle).to_be_greater_than(0)
        expect(metal_readback.device_identity).to_be_greater_than(0)
        expect(metal_readback.pixel_count).to_equal(32)
        expect(metal_readback.checksum).to_be_greater_than(0)
        if directx_pixels.len() > 0:
            expect(metal_readback.pixels).to_equal(directx_pixels)
            expect(metal_readback.checksum).to_equal(directx_checksum)
        metal.shutdown()

step("Inspect native D3D and Metal host checkpoints")
if detect_os() == "linux":
    match Engine2D.create_requested_backend(4, 4, "directx"):
        Err(reason): expect(reason.len()).to_be_greater_than(0)
        Ok(directx):
            expect(directx.backend_name()).to_equal("directx-software-emulation")
            directx.shutdown()
    val metal = Engine2D.create_with_backend_strict(4, 4, "metal")
    expect(metal.is_ok()).to_be(false)
    expect(metal.unwrap_err().requested_name).to_equal("metal")
else:
    expect(detect_os().len()).to_be_greater_than(0)

step("Request an unavailable backend through the strict facade")
val result = Engine2D.create_with_backend_strict(4, 4, "does-not-exist")
expect(result.is_ok()).to_be(false)
val diagnostic = result.unwrap_err()
expect(diagnostic.requested_name).to_equal("does-not-exist")
expect(diagnostic.selected_name == "cpu").to_be(false)
```


Reproduction: the executable source is
`test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl`.
It uses only `Engine2D.create_requested_backend`,
`Engine2D.create_with_backend_strict`, draw/present, and
`read_pixels_with_source`; no fixture backend or middle mock is involved.

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Integration |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_backend_provenance_matrix_spec.spl` |
| Updated | 2026-07-27 |
| Generator | Manual synchronization while the self-hosted checker crash is open |

## Coverage Boundary

Physical NVIDIA/AMD/Intel versus lavapipe qualification requires separate
ICD-selected external runs and is tracked in the external-host TODO. This
integration spec validates translation, native/emulated naming, strict
unavailability, and fallback rejection without pretending one process ran two
devices.

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

</details>
