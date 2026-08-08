# Vulkan Font Atlas Composite Specification

The 22 active scenarios cover the frozen 13-word parameter ABI, bounded
dispatch, atlas replacement, deterministic checksums, exact packed-pixel
parity, artifact admission, cache identity, batch validation, session
ownership, and idempotent cleanup.

The embedded compute artifact is generated from semantics revision 2:

- GLSL SHA-256:
  `ee0e8a35748553891fc82013b09e96abf569072630fed0333e469f20cc1c1162`
- SPIR-V SHA-256:
  `ca5a3d644e5d4dd1c3b6d453be4db252f8ed7b9d65b78e2f7ae37c17769dc55d`
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
