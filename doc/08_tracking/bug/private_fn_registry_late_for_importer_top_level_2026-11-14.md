# private_fn_registry_late_for_importer_top_level_2026-11-14

- **Severity:** P3. **Status:** fixed (`work/private-gate-residuals-20261114`).
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

## Fix

The flattening loader (`pipeline/module_loader.rs`
`load_module_with_imports_internal`) registers a module's private fn names
right after parsing it (`register_module_private_fns`, the same
`private_top_level_fn_names` the interpreter loader uses), so they are known
before any flattened top-level initializer runs. The measured cause was that
a flattened importer's initializers run before the kept `use` statement makes
the interpreter loader evaluate (and register) the imported module. The
registry is now process-wide with a per-thread cache.

Evidence and census: `private_call_gate_skips_import_bound_and_entry_calls_2026-11-14.md`,
"Residuals closed". Matrix rows `topglob`, `topglobmain` (refused) and
`topsame`, `topsamemain`, `toptest` (allowed).
