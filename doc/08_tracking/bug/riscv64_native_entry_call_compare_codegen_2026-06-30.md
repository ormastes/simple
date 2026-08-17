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
