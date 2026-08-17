# Bug: riscv{32,64}-unknown-none native-build crashes — field access on nil receiver (phase3 HIR lowering)

- **Date:** 2026-07-24
- **Severity:** P0 — blocks ALL riscv cross-target builds (NVMe rv32 fw gate, SimpleOS rv32/rv64 kernels)
- **Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` deployed 2026-07-24 01:22
- **Status:** OPEN — WC fix staged (stage4 strict-lane extern fixes in `src/compiler/50.mir/`), bootstrap redeploy in progress

## Symptom

Any `bin/simple native-build --backend llvm --target riscv32-unknown-none --emit-object <file>`
(riscv64-unknown-none identical) dies:

```
runtime error: field access on nil receiver
timeout: the monitored command dumped core
Illegal instruction   (rc=132, SIGILL core dump, phase3 HIR lowering)
```

Reproduces on a 2-line `fn main() -> i32: 0i32` — unrelated to firmware code,
`@naked`, or `asm volatile`.

## Evidence / bisect

- Gate `scripts/check/check-nvme-rv32-minimal-live.shs` proven green 2026-07-07; harness (link + QEMU halves) intact.
- Jul-23 backup binary (`simple.bootstrap-clobber-bak`) does NOT crash (but emits GC-runtime symbols unresolvable in freestanding link).
- Regression window: compiler binary redeploys Jul 22–24; suspect WC file `src/compiler/20.hir/hir_lowering/module_surface.spl`.
- Related deployed-binary defect class: enum/Option decode (see `jit_option_i64_value3_reads_as_none_2026-07-24.md`); nested enum-typed HIR field mis-decode on read (stage4 enum-text tracking 2026-07-24).

## Secondary regression (same window)

Parse slowdown: 180 small generated fw files parse >300 s (progressing, not hung —
phase-profile timestamps advance) vs whole build fitting the 90 s gate budget when
green. Workaround: `NVME_RV32_BUILD_TIMEOUT_SECS=600`.

## Also hit while rebuilding

`bin/simple build bootstrap` via the broken binary fails immediately with
`No entry point specified for native-build backend` (CLI misparse; see
`cli_symlink_argv0_seed_sibling_lookup_2026-07-24.md`). Working rebuild path:
`sh scripts/bootstrap/bootstrap-from-scratch.sh`.

## Verification once fixed

1. riscv32 + riscv64 `-unknown-none` repro compiles clean.
2. `NVME_RV32_BUILD_TIMEOUT_SECS=600 sh scripts/check/check-nvme-rv32-minimal-live.shs` → `ALL RV32 NVME FW CHECKS PASS`.
3. Regression test to add: minimal cross-target compile smoke (rv32+rv64 `-unknown-none`) in the pre-deploy smoke matrix — this class (representation/decode soundness) has recurred; type-checked ≠ sound when enum/struct decode regresses.

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

UNPROVEN by this lane. Every reproduction path for this row is a cross-target/freestanding `native-build` (riscv*-unknown-none / x86_64-unknown-none, LLVM or Cranelift, plus QEMU boot), and the fix sites fall in lanes claimed by concurrent sessions (`src/compiler/20.hir/hir_lowering/**`, `src/compiler/50.mir/**`, `src/compiler/70.backend/**`, `pipeline/native_project/**`). No content-level fix marker was found for it in current source, and no cheap hosted-engine proxy exists — the hosted engines do not exercise the failing path at all. Status left OPEN, unmodified; do not read this note as either a confirmation or a close.
