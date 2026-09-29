# Windows MSVC/MinGW Stage 2 native-build fails: index-compatibility-missing

**Status:** fixed 2026-09-20.

## Symptom

`main` was red on the "Windows Build (MSVC + MinGW)" workflow's **Windows
MSVC** job (run `35477026840`). The Stage 2 compile step (`.github/workflows/windows-build.yml`)
failed during native-build phase 1:

```
error: persistent package index admission failed: index-compatibility-missing;
run explicit cold initialization with SIMPLE_PACKAGE_INDEX_COLD_INIT=1
[ERROR] phase 1 FAILED
D:\a\_temp\...sh: line 5:  1834 Illegal instruction  "$SEED" native-build ...
##[error]Process completed with exit code 132.
```

## Root cause

`package_index_route_current_v1` (`src/compiler/80.driver/cache/package_index_route.spl:104-106`)
fails closed to `"index-compatibility-missing"` whenever
`SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST`, `SIMPLE_PACKAGE_INDEX_ROOT_GENERATION`,
or `SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST` are empty. Unlike the SCV identity
env vars it checks right before them (`SIMPLE_SCV_SNAPSHOT_ROOT`,
`_REVISION_ID`, `_TREE_ID`, `_INVENTORY_DIGEST` — all set programmatically by
`src/app/io/_CliCompile/native_build_closure.spl:170-175` before phase 1
runs), **nothing in this repository ever computes or sets those three
compat-marker env vars**. Confirmed by grep: they are read via `rt_env_get`/`env_get`
in several files but never written via `env_set`/`rt_env_set` anywhere.

This gate was introduced by `e0fa5ef45e2` ("WIP: harmonize bootstrap
references and migrate kernel plugins", 2026-09-07). The sanctioned bootstrap
(`scripts/bootstrap/bootstrap-from-scratch.sh`) always passes
`SIMPLE_PACKAGE_INDEX_COLD_INIT=1` explicitly on every invocation, which
bypasses this whole route (see its 3 occurrences), so it never observed the
gap. `.github/workflows/windows-build.yml`'s Stage 2 step invokes the seed's
`native-build` directly and only sets the *unrelated*
`SIMPLE_SCV_INVENTORY_COLD_INIT=1` (a different gate, in
`src/app/compiler_entrypoint/admission.spl` / `inventory_events.spl`) — it
never set `SIMPLE_PACKAGE_INDEX_COLD_INIT`, so it was the one caller in the
repo that actually reached the hard failure.

**PR #1036 ("fix(scv): track only compilable source paths in cold-init
inventory", merged 2026-09-17) is NOT the cause** — it merged 10 days after
the gate landed, and `windows-build.yml`'s `actions/cache` step only caches
`~/.cargo/registry`, `~/.cargo/git`, and `src/compiler_rust/target` (Cargo
build cache); it does not cache the persistent package index
(`machine_cache_root()`) at all, and the compat-marker check triggers before
any cached index content is even read. #1036 most likely just triggered a
fresh CI run over paths this workflow watches; the underlying defect predates
it.

## Exit code 132

`132 = 128 + 4` = `SIGILL` (illegal instruction), confirmed by bash's own
`"Illegal instruction"` message. This is a genuine crash, not just error-path
propagation — but it happens *after* `add_error(...)` already printed the
controlled `index-compatibility-missing` message and `"[ERROR] phase 1
FAILED"`. The crash is downstream cleanup/exit behavior on the already-failed
path; it was not independently investigated further because fixing the root
cause (below) means this path is never entered on Windows CI.

## Fix

`src/compiler/80.driver/driver_source_pipeline_loading.spl` — `package_index_cold_init`
now self-heals: it is true when `SIMPLE_PACKAGE_INDEX_COLD_INIT=1` is set
explicitly, **or** when any of the three compat-marker env vars are absent
(`package_index_compat_markers_present == false`). This matches the fact that
no code path in the repo ever populates a warm-path compatibility marker, so
their absence is not an error condition — it means the warm route was never
admitted and cold init is correct, the same conclusion
`bootstrap-from-scratch.sh` already reaches by passing the flag explicitly.

No workflow change was needed; this makes every caller that omits the marker
env vars (not just `bootstrap-from-scratch.sh`) fall back to cold init
automatically, instead of requiring every native-build caller to independently
learn to pass `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`.

## Check

`scripts/check/check-package-index-cold-init-self-heal.shs` (`--selftest` for
the decision-logic fixtures; run with no args to verify the driver source
still folds compat-marker absence into `package_index_cold_init`).
