# `if val x = <Result expr>` binds the whole Result instead of the Ok payload

Status: OPEN. Severity: P2. Found 2026-11-07 (lane m-result).

## Observed
`module_surfaces_from_modules` changed from `Option<ModuleSurfacesByName>` to
`Result<ModuleSurfacesByName, text>`. Specs that still wrote
`if val surfaces = module_surfaces_from_modules(...)` kept compiling; the binder
received the whole `Result`, so the first field access failed at runtime with
`semantic: undefined field: unknown property or method 'ordered_names' on Result`
(interpreter, `bin/simple.exe` 2026-11-04). Hit in
`test/01_unit/compiler/result_err_record_owner_spec.spl` (14/15 red) and
`test/01_unit/compiler/mir/result_try_provider_tuple_spec.spl` (10/10 red).

## Expected
`if val` on a non-Optional `Result` should be a compile error (or a defined
Ok-unwrap), never a silent bind of the carrier.

## Repro
```
fn r() -> Result<i64, text>: Ok(1)
fn main():
    if val x = r():
        print(x + 1)   # binds Result, not 1
```

## Workaround applied (callers only)
Both specs now `match ... case Ok(surfaces) / case Err(reason)`. The language
gap itself is not fixed here.

## 2026-11-09 update: fix-implemented-verification-pending
Status: fix-implemented-verification-pending.

Root cause: bare `if val x = e` / `while val` desugar to a presence binding; a
non-optional `Result<T, E>` is not a presence carrier, but nothing rejected it,
so the whole Result was bound.

Fix (landed in commit 60e64b91fc8, "require explicit presence projection for
bare Result bindings"): both compilers reject a bare identifier binding over a
non-optional Result with `cannot bind a Result with bare if val/while val; use
match Ok/Err or Result.ok.?`. `Result<T,E>?` and the explicit `.?` projection
stay allowed.
- Self-hosted: `src/compiler/20.hir/hir_lowering/statements.spl`
  (`validate_presence_binding`).
- Seed: `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` and the
  interpreter in `interpreter_control.rs`; Rust test in
  `hir/lower/stmt_lowering.rs` (Result binding fixture).

Evidence: `test/01_unit/compiler/if_val_result_contract_spec.spl`, run from a
worktree, is 6/6 green; with `statements.spl` reverted to 60e64b91fc8~1 it is
4/6 (2 failed).

Callers: a corpus sweep (every fn whose only declarations return a
non-optional `Result<`, vs every `if val/elif val/while val x = name(...)` in
src/ and test/) found one site, `interpreter_calls.spl:207`, and its callee
returns `Result<..>?` (optional, allowed). The two specs named above were
already converted to `match`. Not detectable by this sweep: `if val` over a
Result-typed variable or parameter (the compiler diagnostic catches those).
