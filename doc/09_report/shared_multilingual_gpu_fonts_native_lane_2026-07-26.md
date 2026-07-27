# Shared Multilingual GPU Fonts — Native Lane Evidence

Date: 2026-07-26
Owner: `native_gpu_perf`
Revision inspected: `744281e7f897b4e7f775b8bc192635c3e6923cfb`

## Current classification

| Row | Status | Evidence or blocker |
|---|---|---|
| REQ-012 | blocked | The source exercises Engine3D atlas texture creation/upload, distinct HUD/world pipelines, texture/sampler binding, vertex draw, fenced submission, device-image readback, depth/placement, translucent-destination, and exact CPU-pixel parity. The canonical native SSpec could not execute because the available full CLI exited 139 before examples. |
| REQ-013 | blocked | This host has discrete Vulkan hardware, but no admitted pure-Simple CLI. Engine2D plus Engine3D promotion therefore has no current authoritative runtime result. |
| NFR-002 | blocked | The exact packed-ARGB CPU comparator and 64×64 absolute device readback are source-covered; runtime proof is blocked by the CLI crash. |
| NFR-004 | blocked | The selected 11-sample, one-warmup, 1,024-glyph 1080p/4K protocol is source-covered; no durable current-host record exists. |
| NFR-005 | blocked | The equal-semantics 4,096-glyph CPU/Vulkan p95 comparison is source-covered; no durable current-host record exists. |
| NFR-006 | blocked | Warm upload counters, paired isolated 2D/3D RSS, and GPU-resource high-water checks are source-covered; no durable current-host record exists. |
| NFR-007 | blocked | Device-loss identity preservation and post-loss CPU p95 checks are source-covered; no authoritative runtime result exists. |
| NFR-008 | blocked | Stage, handle, hash, fence, device-origin readback, and CPU-oracle fields are fail-closed in the v5 record; no current promoted record exists. |

No row is promoted from source inspection, emission, a CPU mirror, or hardware
discovery.

## Host-independent source audit

- Engine2D real-device stages:
  `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl`.
- Engine3D texture/pipeline/draw/fence/readback stages:
  `src/lib/gc_async_mut/gpu/engine3d/vulkan_font_adapter.spl` and
  `src/lib/nogc_sync_mut/engine/render/vulkan_backend3d.spl`.
- Absolute 2D/3D pixel and forged-proof checks:
  `test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl`.
- Selected warm/sample/resource collector and fail-closed v5 parser:
  `test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl` and
  `test/helpers/shared_multilingual_gpu_fonts_perf_evidence.spl`.
- Static placeholder audit found no `pass_todo`, trivial always-true assertion,
  legacy `Given_`/`When_`/`Then_` helper, or compatibility boolean matcher in
  those owned evidence paths.

## Host and retained evidence

- Host: `Linux 6.8.0-124-generic x86_64`.
- Vulkan devices: NVIDIA TITAN RTX and NVIDIA RTX A6000, driver `580.126.16`;
  `vulkaninfo --summary` also reports llvmpipe, which is not promotion evidence.
- Available rejected CLI:
  `release/x86_64-unknown-linux-gnu/simple`,
  SHA-256 `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`.
- Attempted launcher and command:

  ```sh
  SIMPLE_NO_STUB_FALLBACK=1 timeout 180 bin/release/simple test test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl --mode=native
  ```

- Result: exit `139` before any authoritative SSpec summary.
- The attempt did not retain the launcher's resolved binary path and SHA-256.
  It is therefore unverified crash provenance and is not bound to the rejected
  CLI SHA listed above.
- Retained log:
  `build/test-artifacts/shared_multilingual_gpu_fonts/lane-e/native_gpu_font_readback.log`.

## Historical resume contract — superseded

The former lane-E-only test and docgen commands are stale. Use only
[Exact owner commands](shared_multilingual_gpu_fonts_all_items_verification.md#exact-owner-commands)
and its attempt-bound `run_focused_spec` and `run_docgen_spec` helpers. They
provide the authoritative all-items identity, immutability, retention, and
completion contract.
