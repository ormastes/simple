# CPU-SIMD Engine2D RVV native target proof missing

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Resolved — proof evidence recorded; RVV native path proven via native binaries with `vsetvli`, `vmv.v.x`, `vle64.v`, and `vse64.v` instructions.

## Evidence

- `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` records x86_64,
  aarch64, and riscv64 Engine2D SIMD evidence independently.
- Current retained evidence:
  `doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-09.md`.
- Runtime owner `src/runtime/runtime_simd_dispatch.c` now cross-compiles
  x86_64, aarch64, generic riscv64, and `rv64gcv` RVV row kernels when the
  matching C compilers are present.
- Runtime owner `src/compiler_rust/simd/src/detection.rs` now detects RVV on
  Linux riscv64 from `AT_HWCAP` / `COMPAT_HWCAP_ISA_V`.
- The public Simple row facade now builds and executes under QEMU for hosted
  AArch64 and RV64GC Linux. Both probes validate row length and exact
  `0xFF010203` pixel data and exit zero.
- With `SIMPLE_RUNTIME_RISCV64_VECTOR=1`, the tracked RV64 binary compiles
  `runtime_simd_dispatch.c` for `rv64gcv`, runs under vector-enabled QEMU, and
  exits zero only after exact fill/copy checks and at least two native SIMD
  hits. Disassembly contains `vsetvli`, `vmv.v.x`, `vle64.v`, and `vse64.v`.
- The self-hosted hosted-native runtime compiler omitted
  `runtime_simd_dispatch.c`; it now includes that owner so generated binaries
  can link the public Engine2D SIMD row externs.
- The LLVM path now lowers runtime arrays through `rt_array_new` / array
  accessors and carries imported function signatures through HIR and MIR. A
  focused x86_64 native binary calls the public Simple fill-row wrapper, checks
  length and `0xFF010203` pixel data, and exits zero.
- The same focused entry closure emits valid AArch64 and RV64GC ELF objects.
  Target disassembly contains calls to `engine2d_simd_fill_row_u32`,
  `rt_array_len`, and `rt_array_get` on both architectures.
- Hosted cross compilation now selects target C compilers, uses GNU cross
  linker flags, and no longer routes generic RV64 Linux object names through
  the SimpleOS linker.

## Impact

The compiler proves the public Simple path through executable x86_64,
AArch64, and RV64 binaries, including positive RVV hit and instruction evidence
for the opt-in vector build.

## Verification

The retained probe is `test/fixtures/compiler/llvm_simd_row_native_probe.spl`.
Build with RVV enabled, then run on a vector-capable target:

```sh
SIMPLE_RUNTIME_RISCV64_VECTOR=1 bin/simple native-build \
  --source test/fixtures/compiler --source src/lib --entry-closure \
  --entry test/fixtures/compiler/llvm_simd_row_native_probe.spl \
  --backend llvm --target riscv64-unknown-linux-gnu \
  --output build/llvm_simd_row_native_probe_rvv
qemu-riscv64 -cpu rv64,v=true,vlen=128,elen=64 \
  -L /usr/riscv64-linux-gnu build/llvm_simd_row_native_probe_rvv
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

## 2026-08-17 verification — runtime lane

**Verdict: STILL OPEN. Matches the doc's own 2026-08-15 update; out of this lane's scope.**

The remaining gap is the `.spl` detection-branch legs, not
`src/runtime/runtime_simd_dispatch.c` — the QEMU arch-matrix legs already run per
the doc's 2026-08-15 note. Closing it therefore requires edits outside
`src/runtime/**` plus a RISC-V QEMU matrix run
(`scripts/check/check-cpu-simd-engine2d-arch-matrix.shs`), which was not run:
the host was dedicated to a stage-3 bootstrap and a QEMU arch matrix is exactly
the kind of mass run that was forbidden for this session.

**What was NOT proven.** Nothing was executed. No claim is made here about
whether the dispatch C is correct; only that the filed gap is elsewhere.

## 2026-08-17 verification — runtime slice (classified by CONTENT)

**Verdict: STILL OPEN, unchanged from the doc's own 2026-08-15 update.** No
source change was found that would close the `.spl` detection-branch legs, and
the C dispatch file (`src/runtime/runtime_simd_dispatch.c`) compiles clean under
the tree gate (`PASS — 104 file(s) compiled, 0 errors`).

**What was NOT proven — this row was NOT executed.** The reproducer is
`scripts/check/check-cpu-simd-engine2d-arch-matrix.shs`, a QEMU arch-matrix gate.
It was deliberately not run: a stage-3 bootstrap owns this host and is the
user's stated top priority, and a QEMU arch matrix is exactly the kind of mass
run the lane etiquette forbids. No `Results:` line was obtained, so treat this
row as carried forward on the doc's prior evidence, not re-verified.
