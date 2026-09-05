<!-- codex-design -->

# Browser WASM WebGPU Infra Detail Design

## Scope

This design implements the accepted SPipe state for browser-side Simple script,
WASM beside JavaScript, Simple2D/Simple3D WebGPU evidence, and WebGPU portable
compute planning. Final feature/NFR requirement files are still pending user
selection from the options documents, so this document traces to
`.spipe/browser-wasm-webgpu-infra/state.md` and
`doc/03_plan/platform/webgpu_js_wasm_simple.md`.

## Data Shapes

BrowserSession records:

- JavaScript execution state and warnings.
- WASM module records with URL, byte length, validity, status, and script order.
- Simple script warnings for unsupported commands and invalid arguments.
- Current body/title state updated by Simple script commands.

Canvas facade records:

- Simple2D dimensions, fill/text commands, Canvas2D JSON, and WebGPU render
  submission counters.
- Simple3D dimensions, clear/camera/mesh commands, scene JSON, scene byte count,
  scene checksum, and WebGPU scene submission counters.

Chrome draw evidence records:

- Host-adaptive adapter/device/pipeline/draw/pixel evidence for the rectangle
  smoke probe and the WASM Simple3D triangle payload probe.
- `source_origin=wasm-simple3d-payload`, payload byte count, payload checksum,
  and triangle count when the Simple3D wrapper is used, even if the local host
  reports `host-unavailable:*`.

Chrome compute evidence records:

- `backend_target=webgpu`, `source_format=wgsl`, `binary_format=none`.
- Entry name, tool hint, shader validity, output count, readback byte count, and
  mismatch count.
- Explicit host-unavailable status when Chrome/WebGPU cannot run.

Compiler planning records:

- GPU target metadata for aliases and automatic order.
- Portable compute target enum including explicit WebGPU/WGSL source plans after
  the Vulkan dedicated-backend boundary and Metal/CUDA/HIP/OpenCL portable
  source lanes.
- Diagnostics that WebGPU execution requires browser host imports.

## Algorithms

1. Page load extracts script tags in order.
2. JavaScript runs through the existing BrowserSession runtime.
3. `application/wasm` and `wasm` scripts validate bytes, create module records,
   and resume later scripts without becoming JS.
4. `text/simple` scripts parse newline commands. Supported commands mutate
   title/body or append Simple2D/Simple3D evidence. Unsupported commands warn.
5. Simple2D/Simple3D facade submission builds deterministic in-process WebGPU
   evidence: pass counts, draw counts, payload sizes, checksums, and status.
6. Chrome evidence wrappers run only in explicit specs/tools. The draw wrapper
   converts bounded Simple3D triangle payload strings into Electron helper
   environment fields, and both draw/compute wrappers parse JSON from helper
   apps while preserving host-unavailable outcomes.
7. Portable compute WebGPU codegen emits WGSL/source-only plans with host-import
   diagnostics instead of claiming native binary output.

## Error Handling

Parsing failures are deterministic warnings tied to command names and argument
positions. WASM validation failure records invalid status and does not abort JS
execution after the failed module. Chrome helper failures normalize to status
records. Codegen unsupported states return diagnostics, not placeholder kernels.

## Verification Map

| Concern | Evidence |
|---------|----------|
| WASM beside JS | `test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl` |
| Simple script beside JS | `test/01_unit/lib/common/web/browser_session_simple_script_spec.spl` |
| Simple2D/Simple3D WebGPU facade | `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` |
| Chrome WebGPU draw evidence | `test/01_unit/browser_engine/chrome_webgpu_draw_evidence_spec.spl`, `test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl` |
| Chrome WebGPU compute evidence | `test/01_unit/browser_engine/chrome_webgpu_compute_evidence_spec.spl`, `test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl` |
| WebGPU target/codegen planning | `test/01_unit/compiler/semantics/gpu_target_contract_spec.spl`, `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl` |

## Open Requirement Gate

Do not create `doc/02_requirements/feature/browser_wasm_webgpu_infra.md` or
`doc/02_requirements/nfr/browser_wasm_webgpu_infra.md` until the user selects
one feature option and one NFR option. Unchosen options should be deleted at
that time per repo policy.
