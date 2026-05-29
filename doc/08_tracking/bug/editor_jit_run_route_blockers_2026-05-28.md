# Bug: JIT (`bin/simple run`) route blockers for the editor

- **ID:** editor_jit_run_route_blockers
- **Severity:** P2
- **Date:** 2026-05-28
- **Area:** compiler / Cranelift JIT codegen + interpreter-extern bridge
- **Status:** open

## Summary

Running the editor (and similar code) via the Cranelift JIT (`bin/simple run`)
hits several distinct blockers. The native-build (AOT) route is unaffected —
these are JIT-path-only.

## 1. VReg(5) codegen stub-fallback (JIT-only)

`file_modified_time` fails JIT codegen with `Copy: source vreg VReg(5) not
found` and is replaced by an empty stub (`SIMPLE_NO_STUB_FALLBACK=1` makes it a
hard error). Native AOT compiles the same function fine, so the bug is in the
JIT codegen Copy/vreg value-map population, not the MIR. Effect: file watcher
silently no-ops under JIT.

Repro: `SIMPLE_LIB=$(pwd)/src bin/simple run src/app/editor/main.spl -- --tui`
(stub-fallback line appears early in stderr).

## 2. JIT cannot resolve interpreter-extern symbols

After the runtime-symbol name-list gaps were closed, the editor JIT reaches
`rt_compile_to_native_with_opt`, which is an `insert_simple!`-registered
interpreter-host extern (`compiler/src/interpreter_extern/`) with no C-ABI
runtime symbol and an ABI mismatch (tuple `(bool,text)` return / `&[Value]`
args). The JIT has no bridge to call interpreter-externs. Architectural —
needs a JIT↔interpreter-extern bridge design.

## 3. calls.rs alias-map emits un-aliased name

`instr/calls.rs:2362-2369` applies the rt-alias map to the lookup name
(`sffi_name`) but emits the un-aliased `func_name_raw` into the relocation, so
codegen-facing aliases (`rt_file_delete`→`rt_file_remove`,
`rt_print`→`rt_print_value`, `sys_get_args`→`rt_get_args`, ...) miss. Worked
around locally with `#[export_name]` wrappers; the proper fix is to emit the
aliased name.

## Impact / workaround

The editor (and code using these paths) cannot run via JIT today; use the
native-build route. Items 1 and 3 are tractable; item 2 needs design.

## Related work status (2026-05-29)

- `rt_native_eq`/`rt_native_neq` export fix — landed on main.
- 692 runtime-symbol name-list additions + alias wrappers — implemented locally,
  **held** (conflicts with a concurrent `runtime_symbols.rs` refactor on main;
  needs reconcile before landing).
- VReg(5) investigation (item 1) — **blocked pending MIR dump**. Root cause not
  confirmed: `compile_copy` hard-errors when `src` vreg absent from `vreg_values`.
  AOT vs JIT divergence not yet verified empirically (needs
  `SIMPLE_NO_STUB_FALLBACK=1` repro against the Rust seed binary
  `src/compiler_rust/target/bootstrap/simple`). Likely fix locus is whichever
  MirInst defines VReg(5) without calling `vreg_values.insert(dest, …)` in its
  Cranelift emitter. Do NOT add a silent fallback to `compile_copy` without
  confirming VReg(5) is cross-block (in `vreg_vars`) first.
- Item 2 (interpreter-extern bridge) — **architectural, skip** for now. The JIT
  has no mechanism to call `insert_simple!`-registered interpreter-host externs
  (ABI mismatch: tuple return / `&[Value]` args). Needs design before any fix.
- Item 3 (alias-map emits un-aliased name) — **fixed** (2026-05-29).
  Root cause: `referenced_call_names` only inserted raw call names, so when
  Simple code calls e.g. `rt_file_delete`, `referenced_names` had
  `"rt_file_delete"` but not `"rt_file_remove"`. `declare_runtime_functions`
  therefore skipped `rt_file_remove` in `runtime_funcs`. The
  `runtime_funcs.get(sffi_name)` lookup at compile_call line 2616 returned None,
  falling through to the cross-module path which emitted the un-aliased symbol.
  Fix: extracted the alias table into `sffi_alias_target()` in `calls.rs` and
  added alias-target insertion to `referenced_call_names` in `common_backend.rs`.
  The `sffi_name` match in `compile_call` now delegates to `sffi_alias_target()`
  to keep both in sync. Aliases route through the 2616 branch (with correct
  text-arg expansion via `text_arg_indices`) instead of the cross-module path.

## See also

- `doc/08_tracking/feature_request/editor_markdown_editing_subsystem_2026-05-28.md`
  (editor render path — separate, native-route concern).
- `doc/08_tracking/bug/seed_octal_string_escape_misdecode_2026-05-28.md`.
