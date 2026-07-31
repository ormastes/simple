# Device-region readback policy

Executable companion:
`test/03_system/check/draw_ir_web_renderer_region_readback_spec.spl`.

Requirement: AC-8.

## Scenario

`step("Read back the requested device region")` invokes
`expect_region_readback`.

The Engine2D façade takes a typed `RegionReadbackPolicy`. Diagnostic recovery
may return an explicitly classified `full_device` or `host_crop` receipt. A
strict presentation request accepts only `device_region`; it otherwise returns
an empty `strict_device_region_required` receipt and never silently promotes a
CPU mirror.

Vulkan owns the current actual region transfer: it reads only the requested
rectangle rows from the device framebuffer using byte offsets. CUDA and Metal
currently retain their whole-frame readback owners, so diagnostic crops remain
truthfully classified as full-device. Software/CPU paths are host crops.

## Evidence status

Runtime evidence for this new AC-8 system contract is blocked. No hardware
region-readback PASS is claimed here, and no CPU-mirror result is presented as
a strict device-region receipt. The executable companion remains the source
and policy contract until a fresh runtime execution is available.

This manual mirrors the frozen step/helper names and does not replace
executable verification.
