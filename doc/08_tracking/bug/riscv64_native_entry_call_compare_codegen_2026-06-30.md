# RISC-V64 Native Entry Call Compare Codegen

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
