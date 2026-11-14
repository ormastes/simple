# private_fn_registry_late_for_importer_top_level_2026-11-14

- **Severity:** P3. **Status:** open (fail-open, product side).
- **Found by:** `private_call_gate_skips_import_bound_and_entry_calls_2026-11-14`
  (fixture `p_top_init_glob`).

## Symptom

Module `topglob.spl` (in `src/app/other/`) glob-imports `lib_mod` (in
`src/app/sub/`) and calls lib_mod's private `secret_helper()` in a top-level
initializer, either directly (`val TG = secret_helper()`) or through one of
its own fns (`val TG = later()`). When `lib_mod` is loaded only through that
glob import, the call runs with rc 0 and no diagnostic, on both lanes.

The same file is refused (`private fn secret_helper ... is not visible to
.../topglob.spl`) once the entry imports `lib_mod` directly first
(`use app.sub.lib_mod.{open_api}`). The same call made later, from a function
at run time, is refused too.

## Cause (measured, not yet located in code)

A debug print in `gate_private_call` shows that the gate runs with the correct
owner (`lib_mod.spl`) and caller (`topglob.spl`), and still allows the call.
The only remaining way for the call rule to allow it is that `lib_mod`'s
private names are not yet in `PRIVATE_FNS_BY_OWNER`. That registry is filled
by `record_provided_names` after a module's evaluation (`module_loader.rs`
around :1530). Glob-loaded modules evidently reach the registry only after
their importer's top level has run.

## Fix direction

Register a module's private fn names before any importer's top-level code can
run. They are purely syntactic (`private_top_level_fn_names` of the module's
items), so they can be recorded before evaluation. That tightens the rule for
module initializers, so it needs its own census.
