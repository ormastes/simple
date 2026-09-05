# SSpec has no directory-wide prevention-mock scope — test runner has no per-directory config hook

- **Date:** 2026-08-07
- **Severity:** low — documentation/convention gap, not a correctness bug.
  No prevention-mock capability regresses; a scope that was never
  implementable simply stays unimplementable until this unblock condition
  is met.
- **Status:** open, doc-only. Filed as part of
  `doc/03_plan/infra/testing/sspec_prevention_mock_plan_2026-08-07.md` unit
  U4. A convention-based workaround exists (below) and is documented at
  `doc/07_guide/infra/testing/prevention_mocks.md`.

## What's missing

`doc/03_plan/infra/testing/sspec_prevention_mock_plan_2026-08-07.md` designs
"prevention mocks" — mocks whose purpose is to fail a test when a forbidden
call path is taken — at three scopes: per-test (`it`), per-file (spec file),
and directory-wide. Per-test scope is specifiable and landed: `prevent(mockfn,
reason)` / `prevent_at_most(mockfn, n, reason)` in
`src/lib/nogc_sync_mut/spec.spl`, checked IMMEDIATELY at the call site (NOT
"checked at the end of `_execute_it`" — that deferred-arming design was
attempted and found impossible under this interpreter; see
`doc/08_tracking/bug/prevention_mock_deferred_arming_impossible_2026-08-07.md`).
Per-file scope (`prevent_file`) landed only as a documented alias for
`prevent` — true auto-checked file scope turns out to have the **same root
cause** as this record's directory-wide gap: module-level spec state does not
persist from one `it` example to the next under this runner, so a guard
"armed once at the top of the file" cannot be auto-checked after every
example either. **Directory-wide scope is not specifiable today**, because:

- The test runner reads a single **repo-level** config file,
  `config/simple.test.sdn`. The loader is
  `src/lib/nogc_sync_mut/test_runner/test_config.spl`; `find_config_file`
  (line 297) searches only the current, parent, and grandparent directories
  relative to the process's cwd — there is no per-spec-directory config file
  concept, and no mechanism ties a config file's location to the directory a
  given spec file lives in.
- Spec discovery in `src/app/test_runner_new/` has no shared-fixture-per-directory
  hook: nothing automatically loads or runs a "directory setup" file before
  every spec in that directory, the way, e.g., a `conftest.py` would in other
  test frameworks. Confirmed by inspection of `test_runner_single.spl` and
  `test_runner_main.spl` — the only per-spec-file inputs are the spec-header
  directives `# @di_test` and `# @exec_limit <N>` (documented in
  `doc/00_llm_process/layer_expert/test_runner/skill.md`), both parsed
  per-file, not per-directory.

Without one of these, a prevention guard armed in one spec file has no way to
automatically apply itself to sibling spec files in the same directory.

## Current workaround (convention, not enforcement)

Documented in `doc/07_guide/infra/testing/prevention_mocks.md` § "Directory-wide
scope: NOT specifiable today": a `_prevention.spl` helper file placed in the
spec directory, exporting a function (e.g. `arm_dir_prevention()`) that calls
the per-file guard API for that directory's forbidden seams. Every spec in
the directory must import the helper and call the function as the first line
of its body. This is **opt-in per file** — a spec that forgets the import is
silently unprotected, and no existing mechanism (lint, runner, or otherwise)
detects the omission.

## Unblock condition

Directory-wide prevention scope becomes specifiable once ONE of:

1. `src/app/test_runner_new/` spec discovery gains a per-directory
   shared-fixture/setup hook (a file that is automatically loaded/run before
   every spec discovered under that directory), or
2. `src/lib/nogc_sync_mut/test_runner/test_config.spl` gains a
   per-directory (not just repo-root-relative parent-walk) config concept
   that a spec's own directory can be matched against at runtime, with a way
   to carry prevention-guard declarations in that config.

Either would let the runner (rather than each spec author) enforce that every
spec under a directory picks up the directory's prevention guards, closing
the current opt-in gap.

## Related

- Plan: `doc/03_plan/infra/testing/sspec_prevention_mock_plan_2026-08-07.md`
  (units U1-U5; this record covers U4's documented gap).
- Guide: `doc/07_guide/infra/testing/prevention_mocks.md`.
- LLM wiki: `doc/00_llm_process/feature_expert/prevention_mocks/skill.md`.
- Layer expert: `doc/00_llm_process/layer_expert/test_runner/skill.md`.

## Evidence note — 2026-08-17 (CONFIRMED BY CONTENT, still OPEN, doc-only)

Verified by content, not by SHA ancestry. The gap is real and unchanged:

- `grep` for any directory-scoped spec-config hook across
  `src/lib/nogc_sync_mut/spec.spl` and `src/lib/common/spec/**` finds
  **zero** hits for `spec_dir` / `prevent_dir` / `spec_config` / any
  per-directory config file convention. The only `sspec`-namespaced
  constants that exist are evidence-manifest schema names
  (`simple.sspec.evidence.v1`, `simple.sspec.counterpart.v1`,
  `simple.sspec.evidence.ext.v1`) — unrelated to prevention scope.
- `spec.spl`'s own `prevent_file` docstring still states that even
  **file** scope is unachievable under this runner ("module-level spec state
  does not persist from one `it` example to the next"), and
  `prevent_file()` is a plain forwarder to `prevent()`. Directory scope is
  therefore two levels away from anything the runner can express today.

No feature was built (this row was explicitly scoped to verify-and-record).
Nothing to reproduce: there is no code path to run, so no `Results:` line
applies. Remains a design gap; the blocker is upstream of prevention-mock
scope — the runner needs per-example persistence of module-level spec state
before any file- or directory-wide scope can be honest rather than fail-open.
