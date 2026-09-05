# JIT named-fn-as-value guard is narrower than its own doc claims: extern fn names still miscompile

- **Filed:** 2026-08-08
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  `src/compiler_rust/compiler/src/codegen/jit.rs`,
  `JitBackend::first_named_fn_value_load`. Two changes were needed, not one:
  (1) `func_names` now chains `mir.extern_fn_names` as the doc's illustrative
  fix suggested, but that alone was INERT — verified by reproducing the
  segfault again after applying only that change. (2) The actual root cause:
  `Node::Extern` handling (`hir/lower/stmt_lowering.rs`, `self.globals.insert
  (e.name.clone(), ret_ty)`) inserts every extern fn's name into `hir.globals`
  too — that's what makes an extern fn name loadable via `GlobalLoad` as a
  value in the first place — and that insert flows unfiltered into
  `mir.globals`. So an extern fn's name was ALWAYS also a `global_names` entry,
  and the guard's `!global_names.contains(name) && func_names.contains(name)`
  condition short-circuited false on the first half for every extern name,
  regardless of `func_names`. Fix: `global_names` now filters out any name
  present in `mir.extern_fn_names` before the guard's set-membership check.
  Verified: `apply(rt_getpid)` / `apply(rt_string_new_literal)` (bare extern fn
  passed as a value) went from a silent SIGSEGV / silent garbage `i64` result
  to a loud `[INFO] JIT compilation failed ... deferring to interpreter`
  refusal, matching the already-landed defined-fn case (`f06` fixture still
  passes: `f06 marker result=42`). The interpreter fallback for the extern-fn
  case itself then reports `variable 'rt_getpid' not found` — a separate,
  pre-existing interpreter-side gap for this specific value class, not a
  regression from this fix, and out of scope here (the goal was eliminating
  the silent-wrong-answer/crash, which is done).
- **Severity:** High — same silent-wrong-answer shape as the already-fixed
  Defect 2 (garbage pointer returned as an `i64`, process exits 0, no
  diagnostic), just reached through a different name class.
- **Component:** Rust seed JIT —
  `src/compiler_rust/compiler/src/codegen/jit.rs`, guard site
  `JitBackend::first_named_fn_value_load` (called from `compile_module`
  immediately after the `first_lambda_function_impl` / Defect-1 guard).
- **Engine:** JIT (default). The interpreter is unaffected.

## The gap

`first_named_fn_value_load` builds its "is this name actually a function"
check from exactly two sets taken off `MirModule`:

```rust
let global_names: std::collections::HashSet<&str> =
    mir.globals.iter().map(|(name, _, _)| name.as_str()).collect();
let func_names: std::collections::HashSet<&str> =
    mir.functions.iter().map(|f| f.name.as_str()).collect();
...
if !global_names.contains(name) && func_names.contains(name) {
    return Some(func.name.clone());
}
```

`mir.functions` holds only **defined** functions in this module (bodies
lowered here). `MirModule` separately carries `extern_fn_names:
HashSet<String>` — "Names of extern function declarations (e.g.,
`rt_getpid`, `aot_c_file`) ... globals that hold function pointers" (see
`src/compiler_rust/compiler/src/mir/function.rs`, `MirModule` struct doc
comment) — and that set is never consulted here.

A `GlobalLoad` whose name is an **extern** fn (declared via `extern fn` and
present in `mir.extern_fn_names`, not in `mir.functions`) therefore:
1. Fails `func_names.contains(name)` (extern fns are not in `mir.functions`).
2. Also very likely fails `global_names.contains(name)`, since an extern fn
   name is not a `globals` entry either — `mir.globals` is populated from
   `val`/`var` module-level declarations, not `extern fn` declarations.
3. Falls through the guard entirely and reaches
   `compile_all_functions` → the same `emit_global_load` "static method
   reference" fallback / `compile_indirect_call` raw-pointer-deref path that
   Defect 2 was written to catch — for a *defined* function name. Loading an
   **extern** fn name as a value takes the identical lowering path but is
   invisible to the guard's `func_names` set.

The guard's own doc comment describes the fallback mechanism as unconditional
("`emit_global_load`'s ... fallback treats **any** `GlobalLoad` whose name is
not a declared global variable as a function reference"), which is broader
than the set the guard actually checks (`func_names`, defined functions only).
That mismatch between the described scope and the implemented scope is the
bug.

## Unblock condition

Extend the name set the guard treats as "this is a function value, refuse
the module" to include `mir.extern_fn_names`, e.g.:

```rust
let func_names: std::collections::HashSet<&str> = mir.functions.iter()
    .map(|f| f.name.as_str())
    .chain(mir.extern_fn_names.iter().map(String::as_str))
    .collect();
```

(Illustrative only — this doc does not implement the fix; per instructions,
`jit.rs` was not edited as part of this note.)

## No current spec coverage

`test/01_unit/language/jit_lambda_and_fn_ref_value_spec.spl` (referenced by
the Defect-2 doc as the regression lock for the *defined*-function case) does
not exercise an `extern fn` name loaded as a value — the fixtures in
`test/fixtures/repro/compiler/jit_closure/` are all locally-defined functions
(f01-f09, f06 for Defect 2 itself). No spec in the repo currently asserts
behavior for `extern fn` names taken as first-class values under JIT.

**Update 2026-08-09:** a fixture now exists —
`test/fixtures/repro/compiler/jit_closure/f10_extern_fn_as_value.spl`
(`apply0(rt_getpid)`), added as a regression pin (not a `bin/simple test`
spec, since `bin/simple test` is interpreter-only per `.claude/rules/testing.md`
and this defect is JIT-only). Re-verified against the currently deployed seed
binary: `SIMPLE_EXECUTION_MODE=jit` still produces the loud
`... loads a named function as a callable value ...` fallback line (not a
crash or a garbage `i64`), confirming the fix described above is still live.
Both engines then hit the separate, pre-existing `variable 'rt_getpid' not
found` gap noted above — unchanged, still out of scope here.

## Relationship to the guard this doc references

This is not a new defect class — it is the same closure-ABI miscompile
covered by
`doc/08_tracking/bug/jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md`
Defect 2, reached through a name the landed guard (commit `45e0e8d6`) does
not check. File as a narrower, still-open instance of that defect rather than
duplicating its analysis.
