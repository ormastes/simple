# Vulkan Font Atlas Composite Specification

The 22 active scenarios cover the frame header plus seven-word glyph-record
ABI, bounded two-dimensional dispatch, atlas replacement, deterministic checksums, exact packed-pixel
parity, artifact admission, cache identity, batch validation, session
ownership, and idempotent cleanup.

The embedded compute artifact is generated from semantics revision 2:

- GLSL SHA-256:
  `8a5c542279bbd37d03be5b9a2fea636f3171bb68cf4072d87162b382541d4444`
- SPIR-V SHA-256:
  `4b5f44e2803a55f6b94bcb3f443ff1c1d209aca7fe890ce1208a340e5c7358e8`
- Target environment: Vulkan 1.1
- Entry point: `main`

Runtime admission recomputes the complete SPIR-V byte hash and rejects a
different artifact before consulting the retained pipeline cache. Structural
batch, destination, atlas, quad, and packed-parameter validation happens before
accelerated-device and fence admission, so unsupported or malformed input
cannot be mislabeled as a missing-hardware condition.

Promotion requires a precompiled artifact, retained device and driver identity,
an accelerated Vulkan device, fenced submission and cleanup, complete buffer
handles, positive device/readback timing, nonblank changed pixels, and exact
CPU-oracle parity. Runtime GLSL remains diagnostic and cannot be promoted.

Source:
`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl`
