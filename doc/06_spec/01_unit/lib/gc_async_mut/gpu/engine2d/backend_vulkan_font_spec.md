# Backend Vulkan Font Specification

The 22 active scenarios cover the frame header plus seven-word glyph-record
ABI, bounded two-dimensional dispatch, atlas replacement, deterministic checksums, exact packed-pixel
parity, artifact admission, cache identity, batch validation, session
ownership, and idempotent cleanup.

The 22 active scenarios cover the frozen parameter ABI, bounded dispatch,
atlas replacement, checksums, exact packed-pixel equality, promotion classification, full atlas upload,
session lifecycle, artifact validation, batch validation, and idempotent shared
session cleanup.

- GLSL SHA-256:
  `8a5c542279bbd37d03be5b9a2fea636f3171bb68cf4072d87162b382541d4444`
- SPIR-V SHA-256:
  `4b5f44e2803a55f6b94bcb3f443ff1c1d209aca7fe890ce1208a340e5c7358e8`
- Target environment: Vulkan 1.1
- Entry point: `main`

Stage promotion additionally requires retained precompiled artifact identity,
`main` plus program version, batch/payload identity, positive fused queue/device,
fence-observation, readback, and CPU-oracle timing, observed handles, changed
device pixels rather than opaque background pixels, and exact checksum/parity.

An active backend rejects session replacement before dimensions or incoming
session validation, retaining its atlas and reference ownership unchanged. A
fresh backend rejects invalid dimensions before retaining a session. The
one-entry font pipeline cache accepts only the same mode-prefixed SHA-256
artifact identity; another valid SPIR-V artifact fails closed without replacing
the retained shader or pipeline. Complete device/fence/readback evidence becomes
promotion-ready only for `precompiled-spirv`; runtime GLSL remains diagnostic.

Source: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl`
