# RISC-V64 Native Entry Call Compare Codegen

Status: open

Native entry-closure builds for `riscv64-unknown-none` lose calls when a
condition compares a zero-arg extern call directly with an integer literal, for
example `if rt_riscv_nvfs_probe() == 1:`. The emitted object keeps the branch
strings but has no `rt_riscv_*` undefined symbols; the condition is compiled as
a constant. A direct truthy condition, `if rt_riscv_nvfs_probe():`, does emit the
extern call.

Evidence:
- `build/os/simple_rv64_smoke_noopt_probe.o` had only `serial_println` and
  `rt_qemu_exit_success` undefined, even with `--opt-level=none`.
- `build/os/simple_rv64_smoke_truthy_probe.o` emitted the expected
  `rt_riscv_nvfs_probe`, `rt_riscv_smf_cli_probe`, `rt_riscv_smf_cli_load`,
  `rt_riscv_smf_gui_probe`, and `rt_riscv_native_gui_process_render` undefined
  symbols.

Required fix: preserve and lower the call result before binary comparison in
the native-entry frontend/HIR/MIR path, then restore the RV64 smoke source to
the explicit `== 1` checks if desired.

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

UNPROVEN by this lane. Every reproduction path for this row is a cross-target/freestanding `native-build` (riscv*-unknown-none / x86_64-unknown-none, LLVM or Cranelift, plus QEMU boot), and the fix sites fall in lanes claimed by concurrent sessions (`src/compiler/20.hir/hir_lowering/**`, `src/compiler/50.mir/**`, `src/compiler/70.backend/**`, `pipeline/native_project/**`). No content-level fix marker was found for it in current source, and no cheap hosted-engine proxy exists — the hosted engines do not exercise the failing path at all. Status left OPEN, unmodified; do not read this note as either a confirmation or a close.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: MIS-ATTRIBUTED — NOT A 50.mir DEFECT; still open elsewhere.**

No call-vs-literal-compare fold marker exists anywhere under
`src/compiler/50.mir/**`. This doc's evidence is undefined symbols in an object
file from a freestanding native-build, i.e. the native-entry frontend/backend
plus freestanding codegen, not MIR lowering. The `expr_dispatch.spl`
attribution is a triage guess and is not decidable by grep. Status left OPEN and
unmodified; re-attribute away from 50.mir.
