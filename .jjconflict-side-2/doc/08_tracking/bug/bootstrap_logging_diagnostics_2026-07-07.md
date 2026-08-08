---
id: bootstrap_logging_diagnostics_2026-07-07
status: IN_PROGRESS
severity: high
discovered: 2026-07-07
related: src/app/cli/native_build_main.spl
related: src/compiler/50.mir/_MirLowering/bootstrap_globals.spl
related: src/compiler/50.mir/_MirLowering/function_lowering.spl
related: src/compiler_rust/compiler/src/interpreter_sffi.rs
---

# Bootstrap logging diagnostics

## Problem

The bootstrap/native-build loop needed repeated reruns because the first failure
often reported only the final interpreter error, for example:

```text
undefined field 'id': cannot access field on value of type 'nil'
```

That does not say which MIR/HIR function or phase produced the bad receiver.

## Done

- Rust seed: plain IO extern calls routed through `rt_interp_call` now dispatch
  to the interpreter extern table (`print`, `print_raw`, `eprint`,
  `eprint_raw`, `dprint`, `println`, `eprintln`).
- Rust seed: field-access diagnostics already use
  `SIMPLE_DEBUG_FIELD_ACCESS` / `SIMPLE_BOOTSTRAP_DIAG` and cache the env lookup
  with `OnceLock`; receiver and stack strings are built only when enabled.
- Pure Simple native-build parent: worker failures containing
  `undefined field 'id'` now print the rerun hint
  `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1`.
- Pure Simple MIR: free bootstrap MIR progress logs are gated behind the shared
  MIR trace flag instead of printing unconditionally.
- Pure Simple MIR: function lowering caches the trace flag per function/block
  path and guards parameter-symbol `.id` access.

## Remaining items

- Reproduce the next bootstrap failure with
  `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1` and keep the log under
  `build/native_probe/`.
- If the next failure is still a nil `.id`, fix the shared symbol-id extraction
  site rather than adding caller-specific guards.
- If logs still lack the failing function after the rerun, add one more
  env-gated phase marker at the shared lowering entry that loses context.

## Evidence

- `cargo test -p simple-compiler --lib interpreter_sffi::tests::interp_call_dispatches_plain_io_externs --manifest-path src/compiler_rust/Cargo.toml`
- `bin/simple test test/01_unit/app/cli_native_build_main_contract_spec.spl`
- Seed compile checks passed for:
  - `src/app/cli/native_build_main.spl`
  - `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`
  - `src/compiler/50.mir/_MirLowering/function_lowering.spl`

## Runtime verification (2026-07-17)

No single deterministic repro exists for this issue as documented. Source grep confirms the "Done" items are present at tip: `SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1` rerun hint present at `src/app/cli/native_build_main.spl:213`, and `interp_call_dispatches_plain_io_externs` test exists at `interpreter_sffi.rs:837`. The "Remaining items" are open-ended and require a real failure to reproduce; status remains IN_PROGRESS.
