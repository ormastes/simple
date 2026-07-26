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

## Exact resume contract

Prerequisite: lane A publishes an admitted fresh pure-Simple Stage 4 full CLI
path and SHA-256 plus the admitted core-C runtime directory and archive
SHA-256. Admission is still pending. From this worktree, set:

```sh
CLI=/absolute/path/to/admitted/pure-simple
CLI_SHA=<published-cli-sha256>
CORE_C_DIR=/absolute/path/to/admitted/core-c
CORE_C_SHA=<published-libsimple_runtime.a-sha256>
LOG_ROOT="build/test-artifacts/shared_multilingual_gpu_fonts/lane-e/$CLI_SHA"
DOCGEN_ROOT="build/test-artifacts/shared_multilingual_gpu_fonts/docgen/lane-e"
mkdir -p "$LOG_ROOT" "$DOCGEN_ROOT"
```

Verify the published hashes and the single global lane-A calibration under
`build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/`.
`fail.exit` must contain `1` with `test-runner: spec failed` in its retained
streams; `empty.exit` must contain `1` with
`test-runner: no examples executed`. Lane E references that calibration and
must not rerun it. A missing or mismatched artifact keeps all lane-E rows
blocked.

After calibration, run the four current lane-E tests once each:

```sh
"$CLI" run src/app/test/font_evidence_runner.spl -- "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl >"$LOG_ROOT/gpu_font_emission.native.log" 2>&1
"$CLI" run src/app/test/font_evidence_runner.spl -- "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl >"$LOG_ROOT/cuda_generated_font_handoff.native.log" 2>&1
"$CLI" run src/app/test/font_evidence_runner.spl -- "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl >"$LOG_ROOT/native_gpu_font_readback.native.log" 2>&1
"$CLI" run src/app/test/font_evidence_runner.spl -- "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl >"$LOG_ROOT/shared_multilingual_gpu_fonts_perf.native.log" 2>&1
```

Then generate the four mirrored manuals once:

```sh
"$CLI" spipe-docgen test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl --output doc/06_spec --no-index >"$DOCGEN_ROOT/gpu_font_emission_spec.out" 2>"$DOCGEN_ROOT/gpu_font_emission_spec.err"
"$CLI" spipe-docgen test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl --output doc/06_spec --no-index >"$DOCGEN_ROOT/cuda_generated_font_handoff_spec.out" 2>"$DOCGEN_ROOT/cuda_generated_font_handoff_spec.err"
"$CLI" spipe-docgen test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl --output doc/06_spec --no-index >"$DOCGEN_ROOT/native_gpu_font_readback_spec.out" 2>"$DOCGEN_ROOT/native_gpu_font_readback_spec.err"
"$CLI" spipe-docgen test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl --output doc/06_spec --no-index >"$DOCGEN_ROOT/shared_multilingual_gpu_fonts_perf_spec.out" 2>"$DOCGEN_ROOT/shared_multilingual_gpu_fonts_perf_spec.err"
```

Pass requires nonzero examples and an authoritative successful summary; a
signal exit, missing summary, unavailable row, software device, CPU mirror, or
missing `build/shared_multilingual_gpu_fonts_perf/evidence.env` is a blocker.
The durable performance record must pass its v5 hash binding and every selected
numeric budget before NFR-004–008 can be marked pass.
