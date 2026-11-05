# Seed interpreter leaks private (non-pub) names across modules

- **Status:** OPEN (root-caused, fix not landed). P2.
- **Found:** tree_wipe follow-up work (family I4).
- **Layer:** Rust seed interpreter, `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs` `register_definitions`.

## Repro (bin/simple.exe run, seed 2026-11-05)
`app/sub/lib_mod.spl`:
```
fn secret_helper() -> i64:
    42
pub fn open_api() -> i64:
    secret_helper()
```
`app/main3.spl`: `use app.sub.lib_mod.{secret_helper}` then `print secret_helper()`
-> prints `42`, no diagnostic. Glob `use app.lib_mod.*` likewise exposes it.
Language rule (syntax_quick_reference "Visibility"): bare `fn` is private to
its file; only same-path sibling access is in warn-only compatibility mode.

## Root cause
`register_definitions` inserts every `Node::Function` into the process-wide
`global_functions` table and `FUNCTION_OVERLOADS` with no `f.visibility` check,
and named/glob import binding never consults visibility. Any loaded module's
private fn is therefore callable from anywhere. This also hides the native
failure class in `glob_imported_private_fn_lowers_to_unmangled_extern_2026-09-13`.

## Why not fixed in this PR
Closing it means changing the seed's global function registry, which the whole
interpreter tier (and src/lib, ~75k non-pub fns) currently resolves through. A
hard error risks every seed-run spec and the bootstrap; it needs a census first.

## Next step
1. Warn-first: on an explicit `use m.{name}` / glob bind where `m` defines
   `name` as non-pub and does not `export` it, emit one warning per (importer,
   name) unless importer is a same-directory sibling; Rust unit test in
   `interpreter_module`. 2. Census warnings over `bin/simple test` corpus.
3. Flip to error once the census is zero; drop private fns from
   `global_functions` keyed lookups for non-owner modules.
