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

## 2026-11-06 skipped (not attempted)
Needs the warn-first census over the stdlib (~75k non-pub fns) described above; too large for a minimal seed change.

## 2026-11-06 partial: warn-first step 1 landed (work/interp-p2-seed)
`module_loader.rs`: a braced `use m.{name}` naming a top-level private `fn` of `m` (not
re-exported) from a file outside `m`'s directory now prints one
`[visibility-warning] ... private fn ...` per (module, name, importer). Calls still resolve
(no behaviour change). Unit: `module_loader::private_fn_visibility_tests`. Remaining: glob
imports, the census (step 2) and the flip to error (step 3).

## 2026-11-09 call-time gate (work/interp-private-leak)
Status: fix-implemented-verification-pending. `interpreter_call/mod.rs gate_private_call` (P4-overload and P5-flat)
calls `interpreter_module::check_private_call_visibility`: a call that resolves to a private, non-exported top-level
`fn` of module M from a caller in a DIFFERENT directory is a hard error unless the (M|name) pair is in
`scripts/check/private_import_baseline.txt`. This covers glob imports and no-import leaks. Same-directory siblings
and the owner itself are unaffected. Limitation: entry-script callers (`<entry>`, directory unknown) are exempt;
braced imports from the entry are still rejected at import time. Red/green: `private_fn_call_visibility_spec.spl`
(pre-fix seed 1 failed; fixed seed 3/3) and Rust `private_call_visibility_tests` 2/2. Sample of 60 specs under
test/01_unit/{lib,common,compiler/95.interp,app}: zero new visibility errors. Not covered: the pre-existing
`private_fn_import_visibility_spec` fails on both seeds (`{{` fixture escape), unrelated to this change.
Item 4 (self-hosted compiler check) filed as interp_private_names_selfhost_check_2026-11-09.
Baseline census (20181 pairs / 3589 modules): src/lib/nogc_sync_mut 5578, src/lib/common 2624, src/app/llm_caret 1463,
src/os/kernel 1147, src/lib/gc_async_mut 857, src/lib/nogc_async_mut 818, src/app/office 522, src/os/crypto 385,
src/app/devhub 347, src/compiler/10.frontend 313.
