# Vulkan opaque rect-list batching

Executable companion:
`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_list_spec.spl`.

The unit has no frozen `step` or named receipt helper. Its executable contract
is fail-closed: initialization failure calls `fail` with the Vulkan error.
When Vulkan is available, it proves two ordered opaque rectangles collapse to
one device dispatch after clear, uses no CPU fallback, returns
`device_readback`, and exactly matches the software reference pixels.

The companion Draw IR source contract uses the shared frozen names
`step("Submit one backend batch and read device pixels")` and
`expect_backend_batch_receipt`; see
`draw_ir_web_renderer_vulkan_rect_list_contract_spec.md`.
