<!-- codex-research -->
# Browser WASM WebGPU Infra Feature Options

## Option A: Thin Vertical Slice First

Description: Implement Simple script `type="text/simple"`, a Simple 2D facade, and fail-closed WebGPU target metadata.
Pros: Smallest useful end-to-end path; low risk to existing JS/WASM behavior.
Cons: Does not complete full WebGPU processing codegen.
Effort: M, 6-10 files.

## Option B: Browser + Codegen Bridge

Description: Implement Option A plus a WebGPU processing plan object connected to GPU target metadata and codegen diagnostics.
Pros: Directly advances CUDA-like WebGPU generation and backend ordering.
Cons: Touches browser, compiler semantics, and docs together.
Effort: L, 12-18 files.

## Option C: Full Hardware-Oriented WebGPU

Description: Implement browser Simple script/WASM, Simple 2D/3D drawing, and hardware WebGPU processing evidence in Chrome.
Pros: Closest to the full long-term request.
Cons: Host/browser variance and high false-green risk if GPU evidence is weak.
Effort: XL, 25+ files.

