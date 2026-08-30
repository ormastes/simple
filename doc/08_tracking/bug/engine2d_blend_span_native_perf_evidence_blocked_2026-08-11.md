# Engine2D blend-span native performance evidence blocked (2026-08-11)

## Status

OPEN — correctness is covered, but native x86/Arm/RISC-V throughput is not yet
admissible and no 8K/80 fps claim follows from the current seed results.

## Implemented production-path change

`src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` now routes unclipped
image and constant-colour alpha spans through
`engine2d_simd_blend_span_u32` / `engine2d_simd_blend_const_span_u32`.
This removes two temporary row allocations plus gather/scatter loops per row.
Scalar fallback and dirty-span marking remain unchanged.

## Evidence gathered

- A detached clean worktree at revision `89ff647028c` was used because the
  shared worktree has an unrelated unresolved conflict in
  `src/compiler/70.backend/backend/runtime_compiler.spl`.
- Before and after both execute 11 examples in
  `backend_software_simd_spec.spl`: 7 pass and the same 4 native-hit counter
  assertions fail. Pixel composition, transparent-source behaviour, scalar
  fallback, dirty-tile behaviour, and kernel-registry dispatch remain green.
- The four failures are not introduced by the change: the seed reports zero
  native row hits in both revisions.
- `simd_isa_provider_spec.spl` was started once to collect its honest
  scalar-versus-span receipt. It emitted no matching timing or verdict output
  for more than two minutes and was terminated under the runaway guard.
- The deployed executable identifies itself as the Rust bootstrap seed. Its
  interpreter/Rust-bridge measurements are correctness evidence only.

## Blocker

The current test route cannot prove the compiled C/native span symbol is used.
The existing provider spec explicitly states that interpreter and JIT extern
calls use the Rust interpreter bridge. Therefore it cannot prove real AVX2,
SSE2, Neon, or RVV execution, allocations, or throughput.

## Required closure evidence

1. Produce a pure-Simple native-AOT executable whose receipt identifies the
   linked native span provider and reports nonzero per-operation native hits.
2. Compare scalar and selected-provider p50/p95 for 64, 256, 4096, 7680, and
   16384-pixel spans, including opaque, transparent, and mixed-alpha inputs.
3. Retain checksum parity, allocation count, binary/source revision, CPU model,
   ISA, fallback state, and max RSS.
4. Repeat under x86_64, QEMU AArch64, and QEMU RISC-V; RVV compile-only evidence
   is not a performance pass.
5. Run a full 7680x4320 dynamic-frame receipt. The 80 fps gate is p95 <= 12.5 ms
   with checksum/readback proof and no fallback. Frame switching must declare
   its damage percentage and cannot stand in for a full-repaint result.

## 2026-08-12 update

The compiled span ABI now routes mixed image and constant-color partial-alpha
work through the existing allocation-free AVX2/SSE2 and NEON arithmetic
kernels. The C helper/span oracle passes on x86-64 and under AArch64 and
RV64GCV QEMU. This closes the missing compiled-path correctness portion only.
Items 1–5 above remain open because there is still no native-AOT Simple timing
receipt, physical Arm/RISC-V throughput, or full 8K frame evidence.

A direct native x86 C-runtime row receipt is now available for 7,680 pixels and
500 samples: opaque-image p95 12,544 ns, mixed-alpha p95 114,549 ns, max RSS
2,048 KiB, zero checksum mismatches. Linear 4,320-row projections are 54.2 ms
and 494.9 ms respectively, both over the 12.5 ms full-frame budget. This is
useful runtime-kernel evidence but does not close item 1 (native-AOT Simple) or
item 5 (measured full framebuffer). A proposed two-pixel AVX2/NEON bridge was
about 7x slower on mixed alpha and was reverted.
