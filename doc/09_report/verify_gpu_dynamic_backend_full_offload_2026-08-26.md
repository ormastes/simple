# Verification Report: GPU Dynamic Backend and Full Offload

Date: 2026-08-26  
Host: Linux x86_64, NVIDIA TITAN RTX  
Scope: intensive current-state verification; no implementation fixes applied.

## Binary admission

- **FAIL:** `bin/simple --version` reports that the deployed binary is a Rust
  bootstrap seed. It cannot provide production SPipe, docgen, GUI, or web/DB
  evidence.

## Dynamic GPU providers

- **FAIL:** `sh scripts/check/check-gpu-provider-dynload-registry.shs` fails to
  link. `runtime_native.o` does not export `rt_gpu_provider_loaded`, provider
  metadata queries, or the expected dynamically dispatched Vulkan operations.
- **FAIL:** `sh scripts/check/check-metal-provider-dynload-registry.shs` fails to
  link for the same missing registry plus Metal provider operation exports.
- **PASS:** both scripts and the focused CUDA/Vulkan/profile scripts pass `sh -n`.
- **FAIL:** the checkers are ahead of implementation; unchanged-binary provider
  loading is not presently proved.

## ProcessingIR Vulkan/CUDA/Metal

- **PASS:** `sh scripts/check/check-processing-ir-vulkan-break-even.shs
  --self-test` validates the fail-closed receipt classifier.
- **PASS:** the live Vulkan break-even gate executes exact ProcessingIR work on
  the physical TITAN RTX with device-origin readback and zero mismatches.
  Break-even is 65,536 elements: GPU total median 348 us versus CPU 1,343 us.
  At 1,048,576 elements GPU total is 3,443 us versus CPU 22,813 us. At 64
  elements the gate correctly selects CPU (165 us GPU versus 2 us CPU).
- **BLOCKED/FAIL:** `check-processing-cuda-vulkan-native-parity.shs` reports
  `processing_cuda_fill_native_reason=probe-binary-missing`; it cannot prove
  CUDA parity or then reach the Vulkan fault/recovery half.
- **BLOCKED:** native Metal execution requires a prepared macOS host; Linux
  source/emulator evidence is not raw Metal readback.

## GUI, Web, 2D, and WM production routes

- **PASS:** rendering source-coupling guard.
- **PASS:** GUI/web queue/readback classifier self-test.
- **FAIL:** production backend-executed evidence reports
  `simple-bin-forbidden`.
- **FAIL:** production renderer parity reports `simple-bin-missing` and
  `missing-explicit-stage4`.
- **FAIL:** the production GUI/web host GPU queue/readback aggregate times out
  after 120 seconds without a receipt.
- **WARN:** Vulkan/RenderDoc host setup finds the TITAN RTX, NVIDIA driver,
  Electron, and RenderDoc, but resolves evidence paths under another checkout
  (`/home/ormastes/dev/pub/simple`) and rejects this checkout's seed binary.
  That readiness output is not current-worktree production evidence.

## Web and database offload

- **FAIL:** production Simple tests cannot run with the forbidden seed.
- **FAIL:** the current system scenario proves admission decisions and target
  strings only. It does not submit a kernel, wait for a device completion,
  validate device-origin readback, or profile actual web/DB GPU work.
- **FAIL:** existing implementation accepts caller-supplied native-execution
  and candidate-result evidence; it does not prove actual device execution.

## Repository and SPipe guards

- **PASS:** staged numbered-artifact guard.
- **FAIL:** working numbered-artifact guard rejects
  `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs` (unrelated
  dirty work, preserved).
- **PASS:** staged direct env/runtime guard.
- **FAIL:** working direct env/runtime guard finds raw process calls in
  `src/app/cli/native_build_main.spl` (unrelated dirty work, preserved).
- **PASS:** SPipe dev-command routing check.
- **PASS:** generated-spec layout count is zero.
- **FAIL (STUB001):** relevant rendering scan finds
  `expect(true).to_equal(true)` in
  `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl`.
- **BLOCKED:** focused Rust host-dynlib tests waited on another session's Cargo
  build lock and were terminated without claiming a result.

## Verdict

`STATUS: FAIL`

The live Vulkan compute/profile row is strong and passing. The umbrella feature
is not production-ready: provider checkers do not link, CUDA and Metal native
rows are blocked, production GUI/web/WM evidence lacks a Stage4 binary and
times out, and web/DB tests do not execute real GPU work.

## Focused remediation after this report

The provider linker defect was claimed in
`doc/08_tracking/bug/gpu_provider_registry_exports_missing_2026-08-26.md` and
repaired at the canonical `runtime_dynload.c` owner. Subsequent focused runs
passed both provider checkers, including invalid provider rejection, actual
Vulkan/CUDA calls, Metal byte/RuntimeValue adaptation, bounded concurrent
lookup, unload/reload, provider replacement through the unchanged harness, and
no static provider dependency. The rendering placeholder assertion was replaced
with concrete mismatch checks, and a manual-first SSpec was added at
`test/03_system/runtime/gpu_provider_dynamic_load_spec.spl`.

This remediation does not change the report's umbrella `STATUS: FAIL`: an
admitted Stage4 runner, generated SSpec manual, native CUDA probe, native macOS
Metal evidence, production GUI/web/WM evidence, and real web/DB GPU execution
remain outstanding. The focused provider checker reached the session's hard
verify/fix cap before the final COFF/MSVC single-owner guard edit, so that final
edit is intentionally not represented as a fresh PASS.
