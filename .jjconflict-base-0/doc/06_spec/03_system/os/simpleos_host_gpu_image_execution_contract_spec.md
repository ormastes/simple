# SimpleOS Host GPU Image and Text Execution Contract Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

## Scenarios

### Fresh-device Draw IR accepts only preflighted image, text, and embedded work

- Decode resources through the canonical host GPU wire.
- Require a full-target opaque RECT or IMAGE to initialize fresh device memory.
- Admit bounded smaller surfaces only with a real embedding ID. A Vulkan
  parent retains its session into a transparent per-surface framebuffer.
- Admit exact IMAGE commands plus bounded nearest-neighbor COPY and transparent
  src-over after opaque initialization, including opaque images clipped by a bounded named child surface, resolved
  TEXT, metadata-only WM RECT styles, and
  one nonzero-alpha first RECT that initializes a fresh transparent child after
  target/clip, font identity, glyph material, and framebuffer-area work
  preflight. Later translucent RECTs remain rejected.
- Route transient glyph quads through the same checked Vulkan image blend; font
  bytes and atlas/cache state remain owned by the canonical font renderer.
- Route an admitted nonzero-alpha RECT initializer through the same checked
  Vulkan src-over path; opaque RECTs retain the direct rect kernel.
- Read each Vulkan child before present, require device provenance, then apply
  embedding opacity through the checked parent Vulkan blend and release it.
- Reject unresolved, malformed, effect-styled, unsupported, unbounded scaled
  work, source/index arithmetic beyond the checked Vulkan
  shader limits, or target-disjoint work before promotion. Clipping never
  admits an empty intersection or an unnamed child.
- Require device readback, a positive backend handle, and zero skipped commands
  before reporting PASS.

### Completion-unknown Vulkan work fails closed

- Submit the blit through the fenced tri-state helper.
- Discard commands that fail during recording.
- Quarantine dependent resources when completion remains unknown.
- Reject later rendering and return empty completion-unknown readback.

### Standalone and session backends share the validated shader

- Compile `spirv_blit()` in both Vulkan initialization paths.
- Keep the checked exact and nearest-neighbor scaled IMAGE COPY/src-over route common to both
  paths with source dimensions in the validated 15-word/60-byte field layout
  inside the existing 64-byte push payload.

Executable source: `test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl`.
