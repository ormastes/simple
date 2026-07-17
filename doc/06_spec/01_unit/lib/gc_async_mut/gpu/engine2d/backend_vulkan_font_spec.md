# Vulkan Font Atlas Composite Specification

> Manually synchronized on 2026-07-13 because the self-hosted Simple/docgen
> lane is blocked. This is reviewed source evidence, not native execution.

The 22 active scenarios cover the frozen parameter ABI, bounded dispatch,
atlas replacement, checksums, exact packed-pixel equality, promotion classification, full atlas upload,
session lifecycle, artifact validation, batch validation, and idempotent shared
session cleanup.

The portable checker separates candidate compilation, artifact validation, and
pin admission. It records semantics revision 2, runs the selected Vulkan
compiler and `spirv-val` through bounded timeouts, and retains a validated new
candidate with `pinned_verified=false` until tracked pins are independently
updated. The embedded revision-1 SPIR-V remains unchanged and rejected by the
runtime semantics gate.

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
