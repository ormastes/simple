# Vulkan Environment and HAL Communication

Traceability: REQ-013, REQ-014, and NFR-007.

This focused qualification uses the canonical `VulkanSession`, Vulkan SFFI
wrapper, and `VulkanBackend`/Engine2D owners. It does not access the dirty web
producer lane.

## Environment receipt

The environment scenario probes the resolved Vulkan loader, `spirv-as`,
`spirv-val`, validates the retained clear kernel, initializes `VulkanSession`,
and requires a discrete or integrated device with a positive logical handle and
driver identity. Presence alone is not PASS. It writes the machine-readable
receipt `build/test-artifacts/02_integration/rendering/vulkan_environment_hal_communication/environment.receipt`
and classifies the host as
`physical-device`, `emulator`, `software`, or `blocked`; the current scenario
admits only `physical-device`. It also binds the resolved loader path to file
size and SHA-256 and records the exact focused command.

## CPU↔GPU communication

The communication scenario uploads 64 exact bytes, reads them back, dispatches
twice through the retained clear pipeline, downloads 64 exact bytes after each
dispatch, and requires a stable positive device identity and logical handle.
It writes `build/test-artifacts/02_integration/rendering/vulkan_environment_hal_communication/communication.receipt`
with byte counts,
dispatch count, handle, identity, and parity status.

## Rendering and rejection

The rendering scenario clears and draws a 2×2 rectangle through
`VulkanBackend`, requires `device_readback`, a positive backend handle, and all
16 exact pixels. Copy/read requests using handle zero must reject and return no
bytes; they cannot claim GPU provenance.

Run once on a prepared physical Vulkan host:

```text
bin/simple test test/02_integration/rendering/vulkan_environment_hal_communication_spec.spl --mode=interpreter --no-session-daemon
```

The probe is bounded and performs no repository scan or retry loop.
