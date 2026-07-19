# Pure-Simple full CLI crashes or stalls delegating SPipe docgen

Date: 2026-07-18

Status: open

## 2026-07-19 VHDL Result escape repair

The static root-cause candidate for the reported `Result.unwrap_err` escape is
`_simple_labeled_tuple_vhdl`.  It wrapped an already-produced
`assignments: text` value in `Ok(assignments)`, checked that infallible value
for an impossible error, and unwrapped it again on both output branches.  The
native entry path intentionally does not run full HIR inference, so this
unannotated synthetic Result had no recoverable error payload type and escaped
the type-directed MIR Result lowering as `Result.unwrap_err`.

The dead Result wrapper is removed and both branches now consume `assignments`
directly.  A source-contract regression check prevents the wrapper and its
unwrap calls from returning.  This deliberately does not restore
the Cranelift adapter's unsafe leaf-name identity shortcut: custom methods named
`unwrap`, `unwrap_err`, or `unwrap_or` still belong to their receiver type.

Runtime closure evidence remains pending.  The session's three allowed
pure-Simple retry cycles were already exhausted by the preserved exit-139
failure, so this continuation performed static verification only rather than
re-running the known-crashing command.  Closure still requires native MIR or
symbol evidence plus clocked and unclocked labeled-tuple behavioral coverage.

## 2026-07-18 continuation

The pure Cranelift call boundary was missing the LLVM backend's existing
logical-process-extern mapping.  `cl_translate_call` now maps
`rt_process_run`, `rt_process_run_bounded`, `rt_process_run_inherit`, and
`rt_process_run_timeout` to their existing tuple/value facades before declaring
an external import.  A focused source contract covers all four names.

A current pure full CLI rebuilt from an underscore-only isolated workspace:

- binary: `build/native_probe/simple-f1n3-cranelift-abi-fix-safe`;
- result: `1360 compiled, 0 cached, 0 failed`;
- startup: `--version` exits 0;
- exact SPipe docgen: no exit-139 process crash, but after reporting the absent
  sibling driver it made no in-process progress for 120 seconds and was stopped;
- direct tracked Sv39 VHDL compilation: reports missing
  `Result.unwrap_err`, then exits 139 before producing RTL.

The source repair is therefore landed locally but not bootstrap-qualified.
This bug remains open until docgen, one focused test, and one VHDL compile all
exit 0 through a deployed pure-Simple CLI.  A hyphenated temporary workspace
also exposed a separate init-symbol mangling defect at link time; using an
underscore-only isolation path avoided conflating that defect with this ABI
repair.

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
