# Vulkan opaque-rectangle SSBO batching

Executable companion:
`test/03_system/check/draw_ir_web_renderer_vulkan_rect_list_contract_spec.spl`.

Requirement: AC-7.

## Scenario

`step("Submit one backend batch and read device pixels")` invokes
`expect_backend_batch_receipt`.

The Vulkan rect-list shader owns binding 0 as the framebuffer and binding 1 as
a bounded, packed SSBO of opaque rectangle records. One framebuffer-sized
compute dispatch iterates that list in record order, preserving overlapping
rectangle draw order instead of racing independent z-slices. The existing
Vulkan session owns the embedded SPIR-V shader and `pipe_rect_list`; the
backend owns record packing, queueing, descriptor dispatch, and the successful
device-dispatch count.

## Evidence status

The fail-closed hardware unit assertion passed with a fresh self-hosted runtime
and `--assert-ran`: two ordered opaque rectangles after clear produced one
rect-list device dispatch, no CPU fallback, a `device_readback` receipt, and
exact SoftwareBackend parity.

The separate system source-contract attempt crashed in the self-hosted
interpreter before executing its BDD example. It is recorded as a runner
failure, not a passing system result; do not substitute a cached or synthetic
receipt for that missing system execution.

This manual mirrors the frozen step/helper names and does not replace the
executable unit parity assertion.
