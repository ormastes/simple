# CPU-SIMD Engine2D RVV native target proof missing

## Status

open

## Evidence

- `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` records x86_64,
  aarch64, and riscv64 Engine2D SIMD evidence independently.
- Current retained evidence:
  `doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-08.md`.
- On the current x86_64 host, x86_64 passes and aarch64/riscv64 are unavailable
  because target binaries are not supplied.
- Runtime owner file `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs`
  implements x86_64 SSE2 and aarch64 NEON row kernels for fill/copy, but has no
  riscv64 RVV row kernel.
- Simple owner facade `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`
  reports RVV as scalar-correct until native RVV rows exist.

## Impact

The riscv64 lane cannot prove native RVV Engine2D drawing. It can only prove
scalar-compatible output through the shared provider surface.

## Required Fix

Add riscv64 RVV fill/copy row kernels in the runtime owner path, wire the same
hit counter used by x86_64/aarch64, build a riscv64 target binary, then run:

```sh
CPU_SIMD_ARCH_MATRIX_RISCV64_SIMPLE_BIN=<riscv64-simple> \
CPU_SIMD_ARCH_MATRIX_STRICT=1 \
sh scripts/check/check-cpu-simd-engine2d-arch-matrix.shs
```

## Update 2026-08-15 — QEMU arch-matrix legs run; .spl detection-branch legs still blocked

`scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` was run with
`CPU_SIMD_ARCH_MATRIX_TARGET_BUILD=1 CPU_SIMD_ARCH_MATRIX_SKIP_RUN=1
CPU_SIMD_ARCH_MATRIX_ALLOW_PARTIAL=1` (SKIP_RUN because no per-arch `simple`
binaries exist; a canonical bootstrap was concurrently running, so the
host-x86_64 evidence leg was also skipped to avoid `bin/simple` contention).
Results (BUILD_DIR `build/cpu-simd-engine2d-arch-matrix-agent`, overall
`partial / arch-evidence-unavailable`):

- source contract: PASS (NEON + RVV dispatch routes and memmove overlap guard present)
- runtime cross-compile: PASS for x86_64, aarch64, riscv64, riscv64_rvv (`-march=rv64gcv -mabi=lp64d`)
- target-binary legs (C kernels + row scheduling, real guest execution):
  - aarch64: PASS — `ELF ARM aarch64` binary run under `qemu-aarch64 -L /usr/aarch64-linux-gnu`; `ENGINE2D_SIMD_C_TEST: PASS`, `ENGINE2D_SIMD_SPAN_TEST: PASS` (NEON dispatch arm of `runtime_simd_dispatch.c`)
  - riscv64: PASS — `ELF UCB RISC-V` binary built with `-march=rv64gcv`, run under `qemu-riscv64 -cpu rv64,v=true,vlen=128,elen=64`; same two PASS lines (RVV dispatch arm)

So the C-runtime NEON and RVV arms now have real non-x86 execution evidence.
What is STILL not covered: the pure-Simple `detect_simd_level()` Neon/Rvv arms
in `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`. The matrix's
`run_arch` evidence legs report `missing-simple-bin` for aarch64/riscv64:

- Prerequisite: per-arch `simple` binaries at
  `CPU_SIMD_ARCH_MATRIX_AARCH64_SIMPLE_BIN` / `CPU_SIMD_ARCH_MATRIX_RISCV64_SIMPLE_BIN`
  (none exist under `bin/release/` or `build/` as of 2026-08-15).
  Cross toolchains and qemu-user are NOT the gap — `aarch64-linux-gnu-gcc`,
  `riscv64-linux-gnu-gcc`, `qemu-aarch64`, `qemu-riscv64` and both sysroots
  are all present on this host.
