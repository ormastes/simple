# TODO 653 — Admit CUDA-to-DirectX HLSL ProcessingIR and Drawing Readback on Windows

- Status: open / native row blocked on every host that is not a prepared
  Windows DirectX 12 machine.
- Target host/hardware: Windows x86_64 with the Windows SDK D3D12 runtime and debug layer, plus a DirectX 12 compute-capable physical adapter.
  WARP is not admissible; software, emulator, and Linux HLSL source-validation evidence
  cannot satisfy this row.
- Toolchain: DXC available on PATH; admitted source-matched pure-Simple
  `bin/simple`; `SIMPLE_LIB=src`; writable evidence root.
- Exact native resume command:
  `SIMPLE_LIB=src bin/simple test test/03_system/app/simple_2d/feature/processing_cuda_directx_native_spec.spl --mode=interpreter`
- Retained evidence:
  - generated HLSL and compiled DXIL artifacts with hashes;
  - D3D12 command submission, queue, fence-completion, and debug-layer event evidence;
  - rendered output image plus dimensions/format/hash;
  - raw device readback compared with the CPU oracle, with the mismatch count.
- Required result: the HLSL contract (deterministic bindings,
  `RWStructuredBuffer<uint>` output at `u0`, `cbuffer DrawParams` at `b0`)
  compiles to DXIL; native submission succeeds; raw device-origin readback
  exactly equals the CPU oracle (mismatch count 0); unsupported translation
  stays fail-closed.
- Linux unavailable-host result: the host-independent HLSL contract row passes;
  the native row validates this metadata and then calls `fail_test`. Exit zero
  is forbidden while physical DirectX 12 evidence is unavailable.
- Owner: prepared-Windows evidence operator
- Merge owner: root Codex agent
- Final reviewer: normal/highest-capability Codex reviewer
