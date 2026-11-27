# Seed interpreter: a call binds to ANOTHER module's same-named private fn

Status: fixed in the seed interpreter 2026-11-24, pinned by a Rust regression
test through the real module loader. The real spec was NOT re-run with the
helper renamed back (no deployed `bin/simple` on the fixing host) — see
"What was executed".

## Symptom

PR #11199 (merge `e15c1f538f5`): `test/01_unit/lib/gc_async_mut/slang/entrypoints/protocol_media_parts_spec.spl`
defined a private helper `fn _text_part(t: text) -> text`. Under `simple test`
(seed interpreter) 4 of its 11 examples built invalid JSON, because the four
calls inside `it` bodies ran
`src/lib/gc_async_mut/slang/entrypoints/openai/serving/serving_pooling.spl:27`
`fn _text_part(s: text) -> ChatPart` instead. The spec never imports
`serving_pooling`; it is loaded transitively (`openai/api_server.spl` imports it). The PR worked
around it by renaming the helper to `_media_text_part`.

No error was raised: the private-call gate (`gate_private_call`,
`interpreter_call/mod.rs`) exempts callers under `test/`, so the wrong callee
ran silently.

## Root cause

Interpreter path, not the native-project mangler (the #11142 family).

`FUNCTION_OVERLOADS` (`interpreter_state.rs`) is one process-wide table keyed
by the BARE function name; every loaded module's `fn` of that name is pushed
into it, private or not (`interpreter_module/module_evaluator/evaluation_helpers.rs:201`,
`interpreter_eval.rs:649`). Priority 4 of `evaluate_call`
(`src/compiler_rust/compiler/src/interpreter_call/mod.rs`, "Priority 4: Check
overloaded regular functions") handed that whole cross-module set to
`select_overload`, which

1. picks the best-scoring candidate regardless of owner, so another module's
   typed-parameter fn outscores the caller's own untyped one; and
2. on an exact tie keeps the FIRST REGISTERED candidate unless
   `is_current_module_candidate` prefers the caller's — and that predicate
   compares against `CURRENT_EXEC_MODULE`, which is `None` for the entry
   file's top level (an `it`/`describe` body included) and is the INVOKER's
   module inside a closure body. With `None` it never prefers anything.

`_text_part(text)` vs `_text_part(text)` is an exact tie, the call sits in an
`it` body, and — inferred from the order-flip case below, not traced — the
library's fn was registered first. The 2026-11-06 fix
(`seed_interp_cross_module_free_fn_collision_2026-11-06.md`) only covered
calls made from a named function frame.

Measured before the fix (test below, `own * 1000 + theirs`, expected `2102`):
`102102` for the `it`-body, top-level and closure shapes, i.e. the entry's
`_part("ab")` returned the library's `100 + len`. The one shape that passed
declared the entry's fn before the `use`, which only flips registration order.

Not the cause here (by reading, not by a separate experiment): the flat
`functions` map overwrites (`interpreter_module/module_loader.rs:1853`,
`evaluation_helpers.rs:210`). They are last-registration-wins too, but both
registration paths also push into `FUNCTION_OVERLOADS`, so Priority 4 decides
before the flat map is read, and the fn-value / UFCS / pipeline fallbacks that
do read it already go through `caller_own_function`. The fix changes nothing
else and turns the failing cases green, which is consistent with that.

## Rule

A call binds to the calling module's OWN definition first. Another module's
fn is a candidate only when the caller declares no applicable one (or imports
it explicitly — `import_bound_candidate`, unchanged).

## Fix

`interpreter_call/mod.rs`, Priority 4: `select_overload` runs first over the
candidates owned by the lexical caller, and only then over the whole set.
The caller is `lexical_caller_owner()` — `private_call_caller()` (closure
origin stamp, else the executing function's owner, else the entry file)
normalised to the `<entry>` owner key that entry-file fns are recorded under.
The no-candidate-scores fallback uses the same caller instead of raw
`CURRENT_EXEC_MODULE`.

Regression test: `src/compiler_rust/compiler/tests/interpreter_private_fn_cross_module_collision.rs`
(6 cases, each through both the flattening pipeline loader and the run-time
`use` loader: `it` body, `it` body with the other module loaded transitively,
`it` body with the fn declared before the import, entry top level, closure
invoked by the other module, and a non-tie where the foreign fn scores higher).

## What was executed

- The first form of the regression test (5 cases, flattening loader only)
  before the fix: 4 of 5 FAILED (`102102`, expected `2102` / `7102`). The
  transitive case and the run-time `use` loader were added afterwards and were
  NOT run against the unfixed seed. After the fix: 6 of 6 pass on both loaders
  (`cargo test --release -p simple-compiler --test interpreter_private_fn_cross_module_collision`).
- After the fix, also green: `--lib interpreter_call` (50 tests),
  `interpreter_same_name_type_regressions`,
  `interpreter_imported_global_same_name_shadow`,
  `bdd_block_local_shadows_module_global`.
- Pre-existing failures on `release/1.0.0`, identical with and without this
  change (not caused or fixed here): `interpreter_flattened_module_globals`
  (`flattened_context_hooks_preserve_module_owner`,
  `flattened_same_named_global_arrays_remain_owner_isolated`,
  `real_vmm_sparse_init_preserves_active_root`) and
  `interpreter_group_import_module_name_collision`
  (`path_derived_main_namespace_remains_suppressed`).
- NOT executed: `protocol_media_parts_spec.spl` with the helper renamed back,
  and the two specs below. The helper stays `_media_text_part`.

## Possibly exposed specs

Both define a private `_text_part(text) -> text` and were exposed to the same
mis-binding whenever `serving_pooling` is co-loaded:

- `test/03_system/lib/slang/feature/slang_multimodal_live_spec.spl:59`
- `test/03_system/lib/slang/feature/slang_video_live_spec.spl:58`

They need no rename once a seed carrying this fix is deployed.
