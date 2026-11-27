# Lint Lane lintB findings — interpreter + app/os loader sweep (2026-11-13)

Scope: `src/app/interpreter/**` + `*loader*.spl` under `src/app/**` and `src/os/**` (118 files).
Lane branch: `work/lint-interp-loader-20261113` @ e86a4a2e8ba. Lint via seed `./bin/simple.exe lint` (~24 s/file, serial; 13-file baseline sample + targeted verification lints).

## Fixed in this lane

| Class | Before | After | Method |
|-------|--------|-------|--------|
| REQC004 wildcard match arm w/o rationale | 233 bare `case _:` arms (grep, all 118 scope files) | 0 | established idiom `case _("<rationale>"):` (see `src/app/office/*.spl`, `src/compiler/35.semantics/*.spl`); rationale text derived from arm body (pass/Err/None/default) |
| FSK003 bare `.to_u8()/.to_u64()` scalar conversion | 6 (`src/os/apps/sshd/host_key_loader.spl:82,157-160`, `src/app/verify/release_bundle_loader.spl:345`) | 0 | linter-prescribed `as` cast (`byte_val as u8`, `(data[offset + n] as u64)`) |
| `Avoid 'export use *'` | 0 in scope | 0 | none present |

REQC004 verification: `lint src/app/interpreter/ast_convert.spl` post-fix shows zero REQC004 (had 2); zero remaining bare arms grep-wide. Spot re-lints of `expr/arithmetic.spl` (28 sites), `verify/release_bundle_loader.spl` (14), `memory/message_transfer.spl` (6), `call/dispatch.spl` (7) parse clean — no new diagnostics introduced.

## CRASH
None. No rc>=128 and no 60 s hangs across ~25 lint invocations (13-file serial baseline + 6 verification lints + probes).

## ERROR-not-warning (hard lint errors — deferred, NOT fixed)

1. `export_outside_init` — "export statement outside __init__.spl — move to __init__.spl or use pub".
   235 sites in non-`__init__.spl` scope files (334 `export` lines total incl. legal `__init__.spl` uses).
   Top offenders: `src/app/interpreter/ast_convert.spl` (33), `src/os/smf/provider_loader.spl` (22),
   `src/app/interpreter/helpers/debug_simple.spl` (12), `src/app/interpreter/ffi/ast_ffi.spl` (12),
   `src/app/interpreter/ast_convert_expr.spl` (12), `src/app/interpreter/ast_convert_stmt.spl` (10).
   Not fixed: fix (move to `__init__.spl` / `pub`) changes module API surface — architectural, outside lane fix classes.
   Auto-fix label says "(certain)" but the seed `lint` CLI exposes no `--fix` flag to apply it.
2. `primitive_api` (MC-API-001/002) — public API exposes bare primitives
   (`bool`, `i64`, `f64`, `u8`, `[u8]`). 15 in the 13-file sample (e.g. `page_loader.spl:42`,
   `host_key_loader.spl:119,177`); more in `memory/message_transfer.spl:35,414,429`.
   Not fixed: requires semantic wrapper types — architectural.
3. `PARAM-002` — `release_bundle_loader.spl:51,59` LoadedReleaseBundleV2 / LoadedReleaseAdmissionV2
   "reorders, removes, or changes a field" from V1. Looks like an intentional versioned-schema
   contract; flagged for owner review. Not fixed.

## SILENT-GAP / error-infra
1. `REQC001` (`pass_* used without a comment string`) reported at `host_key_loader.spl:0:0` —
   no line locator; no `pass*`/`pass_todo` statement exists in the file (only identifier `pass_dn`).
   Diagnostic locator appears broken for this class; could not find the offending construct by eye.
2. Import-closure re-lint: linting one file re-reports diagnostics for every transitively imported
   file (e.g. linting `page_loader.spl` emits 53 warnings located in `src/lib/**`,
   `src/app/io/cli_lint_commands.spl`, `src/compiler/...`). No dedup across invocations; makes
   per-file "zero warnings" gates noisy and 3-4x slower than necessary.
3. Seed banner: every lint run prints the Rust-seed warning + `[engine-demotion]` line on stdout,
   intermixed with diagnostics (parses as noise in logs).

## Deferred warning classes (in-scope paths, from 13-file sample; full-scope count not completed — timebox)
- `unnamed_duplicate_typed_args` — 10 in 5 files; auto-fix marked "(uncertain)" — needs named-call rewrite, not mechanical-safe.
- `non_exhaustive_match` — 5 in 3 files (e.g. `host_key_loader.spl:36,141`, `page_loader.spl:92`); sanctioned fix adds `todo()` catch-all — semantics change, not in lane classes.
- `COLL006` string concat in loop — 1 (`SerialBatchEventUploader.spl:167`); needs StringBuilder refactor.
- `bare_bool` — 1 (`WorkerStateUploader.spl:44`); needs descriptive enum — architectural.
- `RAW-RT-002` raw `rt_*` intrinsics — observed in `loader_api.spl` (out-of-fix-classes; needs std facade routing).
- `unknown_annotation '@export'` — `loader_api.spl:160` (auto-fix "(likely)" but no CLI `--fix`).
- Unlinted remainder of scope (78 files): not covered by baseline sample; REQC004/FSK003 were swept
  grep-wide, but W-STR-BRACE-001 and other lint-only classes may exist in the unlinted files —
  needs a follow-up full serial pass (~35 min at ~24 s/file).

## Unfixed-but-noted sites
- `.to_i64()` calls on String receivers (`ast_convert_expr.spl:18`, `ast_convert_pattern.spl:16`)
  and enum receivers (`actor_scheduler.spl:105`, `mailbox.spl:94` + specs) look like legit method
  calls, NOT FSK003 bare scalar conversions; left untouched (no lint evidence of FSK003).
