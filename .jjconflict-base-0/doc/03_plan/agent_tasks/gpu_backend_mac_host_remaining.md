# macOS Metal Backend Host Work Remaining

## Scope

This lane is postponed from the current Linux host. It records the work needed
to obtain fresh Darwin evidence; it does not claim that Metal has run here.
The companion system spec is
`test/03_system/gpu/metal_backend_mac_host_spec.spl`.

Linux substitution research and LLM guidance:

- `doc/01_research/domain/linux_metal_emulation_2026-07-30.md`
- `doc/00_llm_process/feature_expert/metal_linux_evidence/skill.md`

## Linux evidence completed before postponement

| Evidence | Check | Status |
|---|---|---|
| Canonical MSL entries and bindings | `metal_msl_pipeline_spec.spl` | implemented |
| Portable Metal emitter shape | `gpu_portable_compute_spec.spl` | implemented |
| Typed Linux Metal rejection | `metal_strict_spec.spl` | implemented |
| Shared strict backend matrix | `native_shader_backend_readback_matrix_spec.spl` | implemented |
| Linux GPU semantic substitute | Vulkan device readback plus CPU oracle checks | implemented |
| SPIR-V to MSL translation | optional SPIRV-Cross diagnostic | tool unavailable on current host; not required |
| Darling Metal loading | optional experimental smoke | tool unavailable on current host; not required |

None of these rows may be relabelled as native Metal execution. The only
remaining Metal evidence class is `macos-metal-live`.

## Exact macOS commands

Run from the repository root on a prepared macOS host. These commands assume
the accepted self-hosted compiler is already present at `bin/simple` and that
the trusted-build manifest exists; this lane does not bootstrap or build it.
The preflight is intentionally fail-closed:

```sh
test "$(uname -s)" = Darwin
test -x bin/simple
test -f build/macos_gpu_2d_live_native/metal/trusted-build.env

xcrun --find metal
xcrun --find metallib
system_profiler SPDisplaysDataType

# Requires the admitted canonical compiler from
# build/macos_gpu_2d_live_native/metal/trusted-build.env. The checker creates
# or verifies its generated-source/metallib toolchain manifest itself via
# scripts/check/check-portable-compute-toolchains.shs.
SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  BUILD_DIR=build/metal_backend_mac_host \
  REPORT_PATH=build/metal_backend_mac_host/report.md \
  sh scripts/check/check-metal-generated-2d-readback.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs

# Windowless MSL compiler/device diagnostic. This is the admitted preflight;
# it stops after MTLDevice + MTLLibrary creation and does not claim dispatch.
# Entry: test/02_integration/rendering/macos_metal_msl_library_micro_diagnostic.spl
SIMPLE_LIB=src \
  sh scripts/check/check-macos-metal-msl-library-micro-diagnostic.shs

SIMPLE_LIB=src bin/simple test \
  test/03_system/gpu/metal_backend_mac_host_spec.spl \
  --mode=interpreter

GPU_2D_LIVE_BACKEND=metal SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  sh scripts/check/check-macos-gpu-2d-live-evidence.shs

SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl \
  --mode=interpreter

SIMPLE_LIB=src bin/simple test \
  test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl \
  --mode=interpreter

SIMPLE_WEB_GPU_PAINT_MEASURE_BACKEND=metal SIMPLE_LIB=src bin/simple test \
  test/05_perf/web_render_chrome/web_gpu_paint_device_measured_spec.spl \
  --mode=interpreter

SIMPLE_WEB_GPU_PAINT_MEASURE_BACKEND=metal SIMPLE_LIB=src bin/simple test \
  test/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.spl \
  --mode=interpreter

SIMPLE_LIB=src bin/simple test \
  test/05_perf/browser/hosted_browser_revision_wire_perf_spec.spl \
  --mode=interpreter

SIMPLE_HOSTED_BROWSER_EXECUTABLE=bin/simple SIMPLE_LIB=src bin/simple test \
  test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl \
  --mode=interpreter

SIMPLE_HOSTED_REVISION_CACHE_BACKEND=metal SIMPLE_LIB=src bin/simple test \
  test/05_perf/browser/hosted_compositor_revision_cache_perf_spec.spl \
  --mode=interpreter

SIMPLE_HOSTED_REVISION_CACHE_BACKEND=vulkan SIMPLE_LIB=src bin/simple test \
  test/05_perf/browser/hosted_compositor_revision_cache_perf_spec.spl \
  --mode=interpreter
```

## Required evidence

- `build/metal_backend_mac_host/evidence.env` has
  `metal_generated_2d_readback_status=pass`.
- The generated lane records `module_verified=true`,
  `submit_attempted=true`, `readback_available=true`, and matching nonzero
  `fill`, `copy`, `alpha`, and `scroll` checksums, with
  `gpu-readback-verified`, `mismatch_count=0`, and `harness_exit_code=0`.
  Its receipt records the admitted trusted-build manifest plus canonical
  Simple, generated MSL source, and metallib paths and matching SHA-256 values;
  caller-overridden Simple or metallib paths must match those admitted values.
- The MSL micro diagnostic records a source SHA-256, positive device/library
  handles, bounded compiler diagnostics, and trusted compiler/provider
  admission. It is a library-creation preflight, not a GPU execution pass.
- The framebuffer and CPU/Metal parity reports identify a real Metal device
  readback, not a CPU mirror or fallback.
- The production `MetalBackend` host scenario enables `gpu_only`, renders the
  16x16 clear/rectangle fixture, and proves exact pixels plus stable positive
  framebuffer handle and device identity across both device readbacks.
- The live runtime receipt records one positive Metal `device_identity` and
  equal initial, Draw IR, and interaction identities; a changed or missing
  identity is rejected.
- The live gate records the native device/queue/submit/readback receipt and
  matching pixels. Linux or unavailable output is not a pass.
- The Vulkan ProcessingIR receipt records 64 exact values, fixed checksum
  `1082179840`, positive handle and identity, zero mismatches, device readback,
  and `cpu_fallback=false`.
- The Metal failure spec completes each bounded fault child without a timeout
  marker and preserves typed unavailable/init/submit/readback/mismatch reasons.
- The web GPU-paint measurement records three paired upload/GPU samples with
  positive p50/p95 timings, exact pixels, and Metal device provenance. Either
  measured route may win; unavailable, mismatched, or CPU-backed evidence fails.
- The primary Draw IR route records three exact paired samples, then reuses the
  completed Metal decision without increasing the sample count.
- The hosted response-route benchmark proves exact alternating red/blue pixels,
  one unchanged reuse after each changed frame, and lower unchanged p50 while
  including render-session work plus response SBRF7 encode/decode.
- The hosted process/pipe benchmark launches the admitted `bin/simple` worker,
  proves producer generation round-trips and worker-owned composition revision
  survives the response pipe, then admits exactly one unchanged reuse after
  every changed reply.
- The hosted compositor revision-cache benchmark records 21 paired forced and
  unchanged frames for both Metal and Vulkan. Each row must report
  `device_readback`, positive stable handle and device identity, exact pixels,
  one admitted reuse per forced render, and
  `hit_p50_ns * 100 < forced_p50_ns * 95`.
- Add canonical device identity plus exact expected-pixel, mismatch-count, and
  max-channel-delta fields before promoting the Vulkan lane from device-capture
  evidence to exact CPU/Vulkan parity.

## Ownership and postponement

- Merge owner: **Codex**.
- Final reviewer: **highest-capability/high model**, read-only after receipts
  exist.
- Postponed because this workspace is Linux and cannot produce Darwin Metal
  device evidence. The current task also forbids bootstrap/full builds; resume
  on a prepared macOS host with an accepted self-hosted `bin/simple` artifact.
- Running the pending system spec or any host-gated wrapper on Linux is only a
  capability check/skip and does not satisfy this lane or produce hardware
  evidence; the TODO remains open until the Darwin receipts above exist.
- Do not close the GPU backend goal or convert this lane to PASS from source
  markers, cached artifacts, or a non-macOS unavailable result.
