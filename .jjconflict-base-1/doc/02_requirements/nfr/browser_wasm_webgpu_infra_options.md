<!-- codex-research -->
# Browser WASM WebGPU Infra NFR Options

## Option 1: Deterministic Software Evidence

Description: Require interpreter-stable object-state, Draw IR, Canvas2D JSON, or WebGPU command evidence; hardware evidence is optional and labeled.
Pros: Portable and reliable.
Cons: Does not prove hardware execution.
Effort: S.

## Option 2: Hybrid Deterministic + Opportunistic Chrome

Description: Require deterministic evidence and add Chrome/WebGPU evidence when `navigator.gpu` is available.
Pros: Stronger browser signal without blocking hosts that lack GPU.
Cons: More harness labeling and maintenance.
Effort: M.

## Option 3: Hardware WebGPU Required

Description: Require Chrome hardware WebGPU execution evidence.
Pros: Strongest proof for browser GPU execution.
Cons: Likely blocks CI/VM/headless environments.
Effort: L.

