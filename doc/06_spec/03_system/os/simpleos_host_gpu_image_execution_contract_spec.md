# SimpleOS Host GPU Image and Text Execution Contract Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

## Scenarios

### Fresh-device Draw IR accepts only preflighted image and text work

- Decode resources through the canonical host GPU wire.
- Require a full-target opaque RECT or IMAGE to initialize fresh device memory.
- Admit exact IMAGE commands and resolved TEXT only after font identity, glyph
  material, target bounds, and the framebuffer-area pixel-work cap preflight.
- Route transient glyph quads through the same checked Vulkan image blend; font
  bytes and atlas/cache state remain owned by the canonical font renderer.
- Reject unresolved, malformed, off-target, scaled, styled, or unsupported work
  before framebuffer mutation.
- Require device readback, a positive backend handle, and zero skipped commands
  before reporting PASS.

### Completion-unknown Vulkan work fails closed

- Submit the blit through the fenced tri-state helper.
- Discard commands that fail during recording.
- Quarantine dependent resources when completion remains unknown.
- Reject later rendering and return empty completion-unknown readback.

### Standalone and session backends share the validated shader

- Compile `spirv_blit()` in both Vulkan initialization paths.
- Keep the checked exact-image route common to both paths.

Executable source: `test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl`.
