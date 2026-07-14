# Vulkan Font Atlas Composite Specification

> Manually synchronized on 2026-07-13 because the self-hosted Simple/docgen
> lane is blocked. This is reviewed source evidence, not native execution.

The 17 active scenarios cover the frozen parameter ABI, bounded dispatch,
atlas replacement, checksums, promotion classification, full atlas upload,
session lifecycle, artifact validation, batch validation, and idempotent shared
session cleanup.

An active backend rejects session replacement before dimensions or incoming
session validation, retaining its atlas and reference ownership unchanged. A
fresh backend rejects invalid dimensions before retaining a session. The
one-entry font pipeline cache accepts only the same mode-prefixed SHA-256
artifact identity; another valid SPIR-V artifact fails closed without replacing
the retained shader or pipeline. Complete device/fence/readback evidence becomes
promotion-ready only for `precompiled-spirv`; runtime GLSL remains diagnostic.

Source: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl`
