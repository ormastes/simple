# SimpleOS Host GPU Image Execution Contract Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

## Scenarios

### Fresh-device Draw IR accepts only checked image work

- Decode resources through the canonical host GPU wire.
- Admit exactly one clipped, full-opacity, fully opaque embedded IMAGE covering the full target.
- Reject empty, mixed, RECT, TEXT, gradient, transparent, missing, or mismatched input before dispatch.
- Require nonempty device readback, a positive backend handle, and zero skipped commands before reporting PASS.

### Completion-unknown Vulkan work fails closed

- Submit the blit through the fenced tri-state helper.
- Discard commands that fail during recording.
- Quarantine dependent resources when completion remains unknown.
- Reject later rendering and return empty completion-unknown readback.

### Standalone and session backends share the validated shader

- Compile `spirv_blit()` in both Vulkan initialization paths.
- Keep the checked exact-image route common to both paths.

Executable source: `test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl`.
