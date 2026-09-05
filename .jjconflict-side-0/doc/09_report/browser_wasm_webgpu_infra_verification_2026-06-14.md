# Browser WASM WebGPU Infra Verification - 2026-06-14

## Status

STATUS: WARN

The current browser/WASM/WebGPU lane has focused evidence for BrowserSession
WASM beside JavaScript, `text/simple` script execution, Simple2D/Simple3D
WebGPU submission records, portable WebGPU/WGSL source-only compute planning,
and Chrome/Electron host-adaptive draw/compute probes.

This is not a release `PASS` because final requirement and NFR documents remain
blocked on user selection from:

- `doc/02_requirements/feature/browser_wasm_webgpu_infra_options.md`
- `doc/02_requirements/nfr/browser_wasm_webgpu_infra_options.md`

## Verified Commands

Run on 2026-06-14 from `/home/ormastes/dev/pub/simple`:

```sh
bin/simple test test/01_unit/lib/common/web/browser_session_wasm_fetch_bridge_spec.spl --mode=interpreter
```

Result: PASS, 2 tests. The run used cache and retained the previous slowest
uncached time of 5925 ms.

```sh
bin/simple test test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl --mode=interpreter
```

Result: PASS, 25 tests. The WebGPU add kernel now emits valid WGSL and the
source-only compile plan uses a `.wgsl` artifact suffix.

```sh
bin/simple test test/01_unit/browser_engine/chrome_webgpu_compute_evidence_spec.spl --mode=interpreter
```

Result: PASS, 6 tests.

```sh
bin/simple test test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl --mode=interpreter
bin/simple test test/01_unit/lib/common/web/browser_session_simple_script_spec.spl --mode=interpreter
```

Result: PASS, 3 tests and 4 tests from cache.

```sh
bin/simple test test/01_unit/browser_engine/chrome_webgpu_draw_evidence_spec.spl --mode=interpreter
```

Result: PASS, 5 tests.

```sh
bin/simple test test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl --mode=interpreter
```

Result: PASS, 1 test from cache.

```sh
bin/simple test test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter
```

Result: PASS, 126 tests. The latest uncached run took 56503 ms and retains bounded
WASM-originated `webgpu.writeBuffer(ptr, len)` memory payload evidence for
byte, halfword, word, Simple2D rectangle payload stores, and exported
`WebAssembly.Memory` buffer reads beside the existing `webgpu.requestAdapter`
and `webgpu.dispatch(x, y, z)` import proofs. It also proves the
`adapter.requestDevice` function shape plus bounded software `device.createBuffer`
and `device.queue.writeBuffer(buffer, ...)` mutation of observable buffer
bytes/counts/checksums, including exported WASM memory bytes `12,13,14`
uploaded through `new Uint8Array(i.exports.memory.buffer)` into a software
WebGPU buffer at offset `4` with checksum `39`. It also proves browser-shaped
software compute submission counters through `createShaderModule`,
`createComputePipeline`, `createCommandEncoder`, `beginComputePass`,
`dispatchWorkgroups(2, 3, 4)`, `finish`, and `queue.submit`, including multi-pass
counter accumulation, invalid active-pass command-buffer filtering, and
WASM-originated `webgpu.dispatch(2, 3, 4)` dimensions forwarded into a compute
pass and submitted as `24` workgroups. Broad-spec runtime still has a
perf follow-up in `doc/08_tracking/bug/browser_webgpu_js_wasm_spec_perf_2026-06-14.md`.

```sh
bin/simple test test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl --mode=interpreter
```

Result: PASS, 1 test from cache.

```sh
sh scripts/setup/install-spipe-dev-command.shs --check
```

Result: `STATUS: PASS spipe-dev-command wiring`.

```sh
find doc/06_spec -name '*_spec.spl' | wc -l
```

Result: `0`.

## Evidence Summary

| Requirement | Evidence | Status |
|-------------|----------|--------|
| Browser WASM beside JS | `browser_session_wasm_script_spec.spl` | PASS |
| Browser `text/simple` beside JS | `browser_session_simple_script_spec.spl` | PASS |
| Fetched WASM -> `WebAssembly.instantiate` -> same-session WebGPU metadata | `browser_session_wasm_fetch_bridge_spec.spl` | PASS |
| Bounded WASM -> WebGPU host imports | `webgpu_js_wasm_simple_spec.spl` covers `webgpu.requestAdapter`, zero-arg `webgpu.dispatch`, WASM-originated `webgpu.dispatch(x, y, z)`, and WASM memory payload handoff through `webgpu.writeBuffer(ptr, len)` using store8/store16/store32 mirrors, Simple2D rectangle bytes `8,12,40,24` plus RGBA `51,102,153,255`, and host reads through `new Uint8Array(i.exports.memory.buffer)` | PASS |
| Browser-shaped WebGPU device queue/compute submit | `webgpu_js_wasm_simple_spec.spl` proves `adapter.requestDevice`, `device.createBuffer`, `device.queue.writeBuffer(buffer, offset, Uint8Array, sourceOffset, size)`, exported WASM-memory `Uint8Array` queue upload, bounded compute encoder/pipeline/pass/submit counters, and WASM-originated compute dispatch dimensions with observable buffer and dispatch evidence | WARN: broad-spec perf still has a follow-up |
| Simple2D/Simple3D WebGPU submission records | `webgpu_js_wasm_simple_spec.spl` | PASS |
| GPU process/codegen order and WebGPU/WGSL source-only target | `gpu_portable_compute_spec.spl` covers portable Metal -> CUDA -> HIP -> OpenCL -> WebGPU ordering, valid compiler-emitted WGSL for `simple_webgpu_add_u32`, and source-only `.wgsl` compile-plan metadata | PASS |
| Chrome WebGPU compute parsing | `chrome_webgpu_compute_evidence_spec.spl` covers explicit generated-source metadata and processing-mismatch classification | PASS |
| Chrome WebGPU draw parsing | `chrome_webgpu_draw_evidence_spec.spl` | PASS |
| Chrome WebGPU draw system wrapper | `browser_webgpu_chrome_draw_evidence_spec.spl` | PASS, host-adaptive |
| Chrome positive hardware WebGPU draw/compute | Host-adaptive system specs | WARN: positive evidence depends on host WebGPU availability |

## Remaining Work

- User must select final feature/NFR options before writing
  `doc/02_requirements/feature/browser_wasm_webgpu_infra.md` and
  `doc/02_requirements/nfr/browser_wasm_webgpu_infra.md`.
- Direct Chrome/Electron WebGPU helper probing on this host is recorded in
  `doc/09_report/browser_wasm_webgpu_chrome_host_probe_2026-06-14.md` as
  `host-unavailable:navigator-gpu` for both draw and compute.
- A complete WASM-originated WebGPU binding ABI remains future bridge work; the
  current lane proves the asset-loading, instantiation, metadata, adapter,
  bounded declared adapter/dispatch/writeBuffer host-import paths, bounded
  exported-memory queue upload, and browser-shaped software compute submit
  counters with WASM-provided workgroup dimensions and memory payload bytes.
- Positive Chrome hardware WebGPU evidence requires a host that returns
  non-fallback adapter/device/pipeline/readback data. Host-unavailable results
  are valid fail-closed evidence, not positive hardware proof.
