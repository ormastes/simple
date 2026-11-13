# Visibility error swallowed by the JIT -> interpreter fallback (2026-11-13)

- **Ids:** `visibility_error_jit_fallback_fail_open_2026-11-13` (P2, fail-open),
  follow-up `jit_main_lane_skips_private_import_visibility_2026-11-13` (P2, open).
- **Found by:** PR #8961 (`private_import_visibility_sweep_2026-11-13.md`,
  "Pre-existing reds").
- **Branch:** `work/visibility-error-fail-closed-20261113` on `release/1.0.0`
  (base `30b4f908889`). **Model:** Opus (Fable unavailable).

## Symptom

```
app/sub/lib_mod.spl:  fn secret_helper() -> i64: 42      (private)
app/main.spl:         use app.sub.lib_mod.{secret_helper}
                      print secret_helper()               (no fn main)
```

`simple app/main.spl` on the seed's default JIT lane printed the visibility
error as an `[INFO] JIT compilation failed, falling back to interpreter` line,
then printed `42` and exited **0**. `SIMPLE_EXECUTION_MODE=interpreter` on
the same file exited 1 with the error, so the fallback was more permissive
than a fresh interpreter run.

## Root cause (two layers)

1. **Loader state leak.** In `interpreter_module/module_loader.rs`, the
   fresh-load path calls `check_private_use_names(...)?` after
   `mark_module_loading(&module_path)` but with no cleanup, unlike the
   evaluation-error arm just above it. The rejected module therefore stayed
   marked "loading". The cache-hit call also skipped `decrement_load_depth`.
2. **Fallback retried a compile-time rejection.** For a main-less file,
   `run_file_jit` evaluates the module on the interpreter itself (the
   `jit-bail:no-main-fn` arm). That run correctly returned the visibility
   error, but `run_file_with_args` treated every non-tagged error as a JIT
   gap and ran `run_file_interpreted_with_args` in the same process. The
   retry found the module still marked loading, took the circular-import
   path (`[loader-trace] circular: .../lib_mod.spl (returning partial)`),
   never re-ran the check, and executed the program.

## Fix

- Loader: on a `check_private_use_names` error, release the loading mark,
  partial exports and load depth exactly like the evaluation-error arm (both
  the fresh-load and the cache-hit call). A retry now re-runs the check.
- Driver: `jit_failure_must_propagate` treats a private-fn visibility
  rejection as fatal (`is_private_fn_visibility_error`), keyed on the shared
  `PRIVATE_FN_VISIBILITY_HINT` constant both producers (import rule and call
  rule) now interpolate. No second execution, one diagnostic. Every other
  JIT failure keeps falling back as before.

## Not fixed here: `fn main` lane

With a `fn main`, the same import runs fully on the JIT with rc 0 and **no**
diagnostic: the pipeline flattening loader
(`pipeline/module_loader.rs::load_module_with_imports`) never runs rule 1, and
no fallback is involved. Porting the rule (baseline, same-directory and test
exemptions) there turns currently-working JIT programs red on a release
branch, so it is filed separately as
`jit_main_lane_skips_private_import_visibility_2026-11-13`.

## Evidence

Seeds built from this tree with `CARGO_TARGET_DIR=.cargo-target-test-private-20261113`;
`before` = base `30b4f908889` (sha256 `ee15b57c552a`), `after` = fix
(sha256 `c03200e9bad3`). Every run `systemd-run MemoryMax=16G timeout 900`, serial.

Root-cause trace (`SIMPLE_LOADER_TRACE=1`, before): the first load prints
`resolve: app.sub.lib_mod`, the fallback's load prints
`circular: .../app/sub/lib_mod.spl (returning partial)`, then `42`, rc 0.

| check | before | after |
|---|---|---|
| main-less fixture (symptom above) | rc 0, stdout `42`, 1 fallback | **rc 1, empty stdout, 0 fallbacks** |
| `private_import_visibility_fail_closed_spec` (new) | 1/2 | **2/2** |
| `private_fn_import_visibility_spec` | 0/1 | **1/1** |
| `private_fn_import_visibility_prevention_spec` | 9/11 | **11/11** |
| `private_fn_call_visibility_spec` | 3/3 | 3/3 |
| `fn main` fixture (follow-up, not fixed) | rc 0, `42` | rc 0, `42` |

Rust (`cargo test -p simple-driver --lib`):
`private_fn_visibility_errors_never_fall_back` and
`private_import_from_other_dir_fails_closed_on_jit_lane` pass. Red probe with
only the loader cleanup removed: the second test fails with
`interpreted retry #0 must still reject: Ok(0)` after the program printed `42`.

**Fallback kept.** Six specs whose child runs take the outer
`[INFO] JIT compilation failed, falling back to interpreter` arm (counted
through a stderr-logging `SIMPLE_BINARY` shim) pass identically before and
after, with the same fallback count:
`jit_named_fn_ref_guard_spec` 3/3 (2 fallbacks),
`function_local_use_enum_scope_spec` 2/2 (1),
`var_rebind_register_spill_spec` 2/2 (2),
`bool_param_literal_admission_spec` 6/6 (4),
`let_literal_type_mismatch_spec` 3/3 (1),
`impl_duplicate_method_spec` 2/2 (1).

**Known nit (review P2, unchanged):** any other error from the main-less
interpreter run inside `run_file_jit` still reaches the outer fallback and runs
the program a second time; only the visibility class is closed here.
