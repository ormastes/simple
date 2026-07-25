# Pure-Simple full CLI crashes or stalls delegating SPipe docgen

Date: 2026-07-18

Status: open

## Summary

A current full CLI built by an isolated pure Stage3 compiler cannot execute
`spipe-docgen`. Normal delegation crashes in `rt_process_run_inherit`; forcing
the existing self-exec guard avoids that crash but leaves in-process source
interpretation CPU-bound until a bounded timeout.

This blocks generated SPipe manuals, focused `test`, and
`md-diagram-update` for the F1/N3 RISC-V FPGA production lane. It must not be
worked around with the Rust seed or a hand-authored manual.

## Build evidence

- Stage3 compiler:
  `build/s3fix2-verify/stage3/x86_64-unknown-linux-gnu/simple`
- Full CLI: `build/native_probe/simple-f1n3-stage3`
- SHA-256:
  `201c54d288764ab9be9649e4f39ce0ce732ea6bd9868703f6e47646fdef385f3`
- Build result: `1358 compiled, 0 cached, 0 failed`
- Build log: `build/native_probe/riscv_f1_n3_stage3_build.log`
- Link warning: unresolved generated stubs include startup/path helpers.

## Reproduction A — delegated execution crashes

```bash
build/native_probe/simple-f1n3-stage3 spipe-docgen \
  test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl \
  --no-index
```

Observed: exit 139, no generated manual. GDB reaches
`__memcpy_avx_unaligned_erms` from `rt_process_run_inherit`, then
`io.process_ops.process_run_inherit`; the stack is corrupt after the runtime
frame. Before the crash, `_cli_driver_binary()` reports that the sibling
`simple_seed` is absent and falls back to workspace `bin/simple`.

Evidence:

- `build/native_probe/riscv_f1_n3_spipe_docgen.log`
- `build/native_probe/riscv_f1_n3_spipe_docgen_gdb.log`
- `build/native_probe/riscv_f1_n3_spipe_docgen_isolated.log`

## Reproduction B — self-exec guard stalls

Pointing `SIMPLE_BOOTSTRAP_DRIVER` at the current executable makes
`_cli_driver_binary()` return empty and selects in-process `interpret_file`:

```bash
full_cli="$PWD/build/native_probe/simple-f1n3-stage3"
timeout 120s env SIMPLE_BOOTSTRAP_DRIVER="$full_cli" \
  "$full_cli" spipe-docgen \
  test/03_system/app/hardware/feature/riscv32_riscv64_fpga_simpleos_production_spec.spl \
  --no-index
```

Observed: one CPU remains busy for 120 seconds, stdout/stderr remain empty, the
timeout ends the process, and no manual is generated.

Evidence: `build/native_probe/riscv_f1_n3_spipe_docgen_inprocess.log`.

## Required repair

1. Repair the pure-Simple `[text]` argument ABI at
   `rt_process_run_inherit`, or route file delegation through a proven facade
   that preserves owned command and argument storage.
2. Make missing sibling/fallback selection fail closed rather than invoking a
   forbidden Rust bootstrap for normal tooling.
3. Diagnose the in-process `interpret_file` non-convergence with the retained
   Stage3 cache; do not launch another cold full-tree worker first.
4. Rebuild one current pure full CLI and require zero startup-reachable
   generated stubs.

## Closure criteria

- The current pure full CLI runs the exact SPipe docgen command once with exit
  0 and creates the mirrored Markdown manual.
- The same CLI runs a tiny source entry and one focused test without delegation
  recursion, exit 139, interpreter fallback, or timeout.
- `md-diagram-update` renders one fixture and the four F1/N3 phase documents.
- The Rust seed is used only to bootstrap a pure compiler and never supplies
  normal command execution.
