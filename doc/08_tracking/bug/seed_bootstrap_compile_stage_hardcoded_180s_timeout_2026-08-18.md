# Seed `build bootstrap` hardcodes `--timeout 180` and a non-canonical `--source` set

- **Filed:** 2026-08-18
- **Status:** FIXED 2026-11-11 (lane p3-comp10) — budget configurable in source since ea948d92a9ae; tracked seed binary carries the fix
- **Related:** `build_bootstrap_planner_flags_silently_ignored_2026-08-18.md`

## Symptom

Stage 1 of the Rust seed's `simple build bootstrap` pipeline dies at ~180s:

```
error: native-build worker timed out after 180s before producing a binary.
  The interpreted worker loads the whole compiler + LLVM import graph before any
  codegen; a large --source set (e.g. src/os + src/lib) exceeds the budget.
  Raise --timeout, shrink --source, or use the in-process backend for cross-target builds.
Compile failed (exit Some(255)) / Stage 1 FAILED / RC=1
```

A second reproduction on 2026-08-18 ended as `exit code 143` (SIGTERM at the same
budget) rather than the worded timeout — same cause, different reporting path.

## Finding

The 180s budget is **hardcoded**, not configured by the bootstrap lane:

- `src/compiler_rust/driver/src/cli/commands/misc_commands.rs`, `compile_stage()`
  passes `--threads 1 --timeout 180 --source src/app --entry
  src/app/cli/bootstrap_main.spl --entry-closure` in **both** branches
  (`is_rust_driver` and self-hosted). There is no flag or env var to change it;
  `handle_bootstrap` exposes only `--backend/--output/--seed`.
- The **canonical** lane, `bootstrap_native_build_main()` in
  `scripts/bootstrap/bootstrap-from-scratch.sh:1062-1080`, passes **no
  `--timeout` at all** (default budget) and a much larger source set:
  `--source src/compiler --source src/app --source src/lib --source
  examples/10_tooling`, plus `--runtime-bundle core-c-bootstrap --low-memory
  --mode one-binary --threads ${selfhost_jobs} --cache-dir …`.

So the failing path is the seed's **ad-hoc** 3-stage pipeline, which is neither
the gated bootstrap nor configured like it: it caps a whole-closure interpreted
build at 180s with `--threads 1`.

## Why not fixed here

Proving "raise the timeout to N and Stage 1 passes" requires actually running a
full seed Stage 1 to completion, which this lane is forbidden from doing (another
lane owns bootstrap). Bumping the constant without that measurement would just
move the failure. Recommended fix, for whoever owns the bootstrap lane:

1. Make the budget configurable (`--stage-timeout=<s>`, defaulting to the
   canonical lane's default = unset) instead of a literal `180`.
2. Better: have `simple build bootstrap` delegate to
   `scripts/bootstrap/bootstrap-from-scratch.sh` rather than maintain a second,
   differently-configured pipeline that no gate covers.

## Hypothesis, for coordination (not verified)

A separate lane is investigating `source_closure 0/0` (zero source discovery) in
native-build. These **may** share a root cause in source-set computation: this
path passes `--source src/app` only and relies on `--entry-closure` to pull in
`src/compiler`, whereas the canonical lane names all four roots explicitly. If
closure expansion under-discovers, the seed path would both under-build and spend
its whole budget in import-graph loading. Stated as a hypothesis; the
source-closure discovery code was deliberately **not** edited by this lane.

## Triage 2026-11-03 (boot-script-fixes lane)

Deferred: the literal lives in the Rust seed (src/compiler_rust/driver/.../misc_commands.rs compile_stage), outside the script/cli scope of this lane, and the fix is only provable by a full seed Stage 1 run. Still open.

## Triage 2026-11-11 (lane p3-comp10)

Verdict: FIXED-at-tip (source). Fresh re-verification at lane base 79d5af6723f6
(release/1.0.0 tip):

- Root-cause fix landed 2026-11-09 as ea948d92a9ae
  ("fix(seed): make bootstrap stage native-build timeout configurable
  (SIMPLE_BOOTSTRAP_TIMEOUT)"), an ancestor of the lane base. The literal
  `--timeout 180` is gone from `compile_stage()`
  (src/compiler_rust/driver/src/cli/commands/misc_commands.rs): both the
  `is_rust_driver` and self-hosted branches now pass
  `--timeout bootstrap_timeout_secs()`, where `bootstrap_timeout_secs()` reads
  `SIMPLE_BOOTSTRAP_TIMEOUT` (positive integer; default 180). The same commit
  replaced the literal `--threads 1` with `bootstrap_threads()`
  (`SIMPLE_BOOTSTRAP_THREADS` override, default half the host cores capped at 8),
  addressing the "whole-closure interpreted build capped at --threads 1" part of
  the symptom.
- Regression tests in-tree: `mod bootstrap_timeout_tests` in the same file cites
  this bug doc id — `default_is_180`, `override_is_honoured` (900 / " 60 "),
  `invalid_or_zero_falls_back` ("0"/"abc" → 180).
- Deployed-seed check: the tracked seed binary bin/simple.exe (build commit
  46fe8f6b6def, 2026-11-10 — itself a descendant of ea948d92a9ae) embeds the
  `SIMPLE_BOOTSTRAP_TIMEOUT` env string (strings probe), so the deployed seed
  carries the fix.
- Not run in-lane: (a) `cargo test` on the driver crate (full seed dependency
  closure build, exceeds the lane's small-build budget) — unit tests listed above
  are the pin; (b) a full seed Stage-1 run proving "raise the budget and Stage 1
  passes" — the doc's own "Why not fixed here" says that requires a full seed
  Stage-1 run owned by the bootstrap lane, and entry-closure native builds are
  forbidden in this lane. bug_db.sdn row stays
  "fix-implemented-verification-pending" for that full-run acceptance.
- Residual (bootstrap-lane acceptance, not this defect): the ad-hoc path still
  passes only `--source src/app --entry-closure` (vs. the canonical lane's four
  named roots), and the doc's preferred remedy #2 (delegate `build bootstrap` to
  scripts/bootstrap/bootstrap-from-scratch.sh) is not implemented; the row's
  filed defect — a hardcoded budget with no override — is fixed.
