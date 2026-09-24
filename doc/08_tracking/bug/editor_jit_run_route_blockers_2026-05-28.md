## Triaged 2026-09-13 — LEFT OPEN, blocked by masking HIR-lowering issue

Status: OPEN, RE-TRIAGED 2026-09-13 — the three filed items are NO LONGER OBSERVABLE because an EARLIER blocker now masks them. Measured on Windows x86_64 with seed `bin/simple` v1.0.0-rc.1: `SIMPLE_LIB=$(pwd)/src bin/simple run src/app/editor/main.spl -- --tui` exits 1 and the only JIT diagnostics emitted are `[jit-fallback] HIR lowering error: Unsupported feature: cannot infer field type while lowering gui_shell_run_sdl: struct ANY field window_title [in src/app/editor/main.spl]: whole module dropped to the interpreter (expect ~100-1000x slowdown)` followed by the matching `[INFO] JIT compilation failed, falling back to interpreter`. Neither `Copy: source vreg VReg(5) not found` (item 1) nor `rt_compile_to_native_with_opt` (item 2) appears at all — HIR lowering aborts the whole module before codegen runs, so those two cannot be confirmed either fixed or still broken from this repro. Item 3 was NOT re-verified: `codegen/instr/calls.rs` has been restructured since filing (`func_name_raw` at :3076, `sffi_name` at :3104-3105, `let func_name: Status: - partial (item 3 fixed; item 1 diagnostic tooling added; item 2 deferred)str = func_name_raw;` at :3109) and the cited line numbers 2362-2369 no longer point at the described code. Left OPEN, with the new masking blocker (`ANY`-typed `window_title` field inference in `gui_shell_run_sdl`) as the actionable next step; it must be cleared before items 1 and 2 can be re-measured.

---

# Bug: JIT (`bin/simple run`) route blockers for the editor

- **ID:** editor_jit_run_route_blockers
- **Severity:** P2
- **Date:** 2026-05-28
- **Area:** compiler / Cranelift JIT codegen + interpreter-extern bridge
- **Status:** OPEN, re-triaged 2026-09-13 — see the Status line at the top of this file; the three filed items are masked by an earlier HIR-lowering blocker and could not be re-measured.

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
- VReg(5) investigation (item 1) — **diagnostic tooling added** (2026-05-29).
  Auto-dump now fires on any "source vreg" compile error, printing post-inline
  MIR to stderr without needing `SIMPLE_NO_STUB_FALLBACK=1` or `SIMPLE_DUMP_MIR`.
  Also added `SIMPLE_DUMP_MIR=<name-filter>` env var for targeted pre-compile
  MIR inspection.
  Static analysis ruled out: (a) missing `vreg_values.insert` in any MirInst
  codegen arm; (b) broken `terminator.uses()` / `inst.uses()` in liveness.
  Revised root-cause hypothesis: the "JIT-only" framing likely reflects DCE
  omitting `file_modified_time` from the AOT editor build rather than a backend
  divergence — `compile_function_body` and `inline_small_pure_functions` are
  shared. The bug surfaces after multi-level inlining (e.g. `file_exists_mock`
  → `file_exists` → caller chain) introduced by the "inline non-tail calls" fix
  (commit 4a97bf5). The Copy-from-Return VReg synthesised by `remap_terminator`
  in mir_inline.rs may land in a cross-block position that the Variable-based
  SSA sync does not yet handle correctly for every callee shape.
  Root cause is NOT yet confirmed empirically.
  Next step: run `SIMPLE_LIB=$(pwd)/src bin/simple run src/app/editor/main.spl
  -- --tui` against the seed binary; the auto-dump will print the exact MIR and
  the undefined VReg's defining instruction (or lack thereof). Do NOT add a
  silent fallback to `compile_copy` — that would silently propagate garbage.
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

- `doc/08_tracking/feature/editor_markdown_editing_subsystem_2026-05-28.md`
  (editor render path — separate, native-route concern).
- `doc/08_tracking/bug/seed_octal_string_escape_misdecode_2026-05-28.md`.
