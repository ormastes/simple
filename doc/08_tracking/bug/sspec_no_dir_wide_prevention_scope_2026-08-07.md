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

## Triage 2026-09-13
Reconfirmed: low-severity documentation/convention gap per this record
(test runner has no per-directory config hook). Not a correctness bug;
needs a runner feature addition. Left as-is, no code change attempted.
## Re-check 2026-09-13 (BUGFIX-12 shard 22)

`src/lib/nogc_sync_mut/spec.spl` still has `prevent_file()` as a plain
forwarder to `prevent()`, and no per-directory config/setup hook exists in
`src/app/test_runner_new/` or `test_config.spl`. This is an architectural gap
in the test runner (per-example persistence of module-level spec state),
explicitly scoped as "verify and record" with no code path to reproduce —
out of scope for a shard fix. No change made. Leaving OPEN, doc-only.

## 2026-11-04 — LANDED: `_prevention.sdn` directory-wide policy (lane work/feat-sspec-dir-prevention-20261104)

Status: **closed by feature** (unblock condition 1 above — a per-directory
hook in spec discovery/launch — is now met).

### Design note

- **Policy file is data, not code: `_prevention.sdn`.** A `_prevention.spl`
  would have to be *imported* by the spec child; there is no runtime
  module-load-by-path, the only path-based `use` form in the tree is
  `use test.fixtures...` (digit-leading segments such as `01_unit` are
  untested grammar), and splicing a `use` line into the runner's rewritten
  spec copy would shift every reported line number. The policy is a list of
  `(mock name, budget, reason)` anyway. The file is an sdn subset parsed
  line-by-line in `src/lib/nogc_sync_mut/spec/dir_prevention.spl` (the full
  sdn parser is not imported into `spec.spl`, which every spec child loads).
- **Merged root->leaf, not nearest-wins.** The runner walks from the spec's
  directory up to `test/` (or the filesystem root, max 24 levels), collects
  every `_prevention.sdn`, and joins them with `;` into
  `SIMPLE_SPEC_DIR_PREVENTION`. A nested directory can add rules; it cannot
  silently cancel a parent's. Resolution is cached per directory
  (`dir_prevention_env_value`, one walk per directory, misses counted).
- **Two dispatch sites set/restore the variable**: the lane `match` in
  `test_runner_main.spl` (directory targets, `[route] mode=...`, every
  lane's child inherits it) and the direct single-file lane in
  `test_runner_single.spl` `main` ("light daemon requires Linux /proc;
  running directly on windows"). Both are runtime-verified below. The first
  attempt set the env inside `run_test_file_interpreter`, a name defined in
  both `src/lib/nogc_sync_mut/test_runner/` and `src/app/test_runner_new/`;
  with marker prints in BOTH copies neither ever printed on the directory
  lane (which still reported 0 failures), so the set moved up to the
  dispatcher where it is lane-agnostic. The restore keeps a later
  policy-free spec from inheriting it.
- **Check mechanism (spec side).** Under the seed `describe`/`it`/
  `before_each`/`after_each`/`fail_assertion` are intrinsics
  (`interpreter_call/bdd.rs`): a print added to `spec.spl`'s `_execute_it`
  never appeared under `simple run`, so the hook point is hook
  *registration*. `spec.spl` registers a before/after_each pair from its own
  module initialiser (`val _dir_prevention_armed = _dir_prevention_init()`,
  last statement of the file) when the env var is non-empty; verified to
  wrap every example and to fail the current example from `after_each`
  (`fail_assertion` sets `BDD_EXPECT_FAILED`, which is read after the after
  hooks: probe gave `2 examples, 2 failures`). Under the self-hosted binary
  the same two calls land in `spec.spl`'s own `before_hooks`/`after_hooks`.
- **Non-vacuity.** `MockFunction.new` (`builder.spl`) records every instance
  in a module-level auto-registry, enabled only when a policy is present
  (`mock_auto_registry_enable`), so a policy-free process is byte-for-byte
  unchanged. `before_each` snapshots each registered mock's call count;
  `after_each` fails the example when `count - baseline` exceeds a matching
  rule's `at_most` (default 0). Per-example delta, so a mock reused across
  examples is not double-counted.
- **Engine traps hit and designed around (not fixed here):** (1) a file
  read or a cross-module global write issued while `spec.spl` is still
  initialising silently does nothing under the seed — every text-read
  provider (`io_runtime.file_read`, `file_ops.file_read`,
  `file_read_result`) died at the call with no error while `env_get` and
  `file_exists` worked; the policy load and registry enable therefore run
  lazily in the first `before_each`. (2) a named constructor argument spelled `mock:`
  fails to parse ("expected Comma, found Colon") and renaming the field to
  `mock_name` fixed it — the parser was not read to confirm why, so this is
  an observation, not a grammar claim. (3) private helper names are
  resolved last-wins across co-loaded modules (`_dir_of` already exists in
  two other modules), hence the `_dprev_` prefix.
- Residual (stated in the guide): mocks built before the first example
  (module level, `before_all`) are outside the per-example window; native/SMF
  lanes do not set the variable; a hand `simple run` needs it set explicitly.

### Evidence (seed `D:/dev/wt/seed/simple.exe`, release tip, class-ref on)

RED -> GREEN on the fixture `test/fixtures/dir_prevention/policy_dir/`
(`_prevention.sdn` + `guarded_example.spl`, which declares no guard):

| run | before feature | after |
|---|---|---|
| `SIMPLE_SPEC_DIR_PREVENTION=<policy> simple run guarded_example.spl` | `4 examples, 0 failures` (env var had no consumer) | `4 examples, 2 failures` — `forbidden_seam called 1x in this example (allowed 0)`, `budgeted_seam called 3x in this example (allowed 2)` |
| same, no env var | `4 examples, 0 failures` | `4 examples, 0 failures` (unchanged) |
| runner e2e, file target (single lane): fixture copied as `guarded_spec.spl` beside its `_prevention.sdn`, `simple test <file>` | `Results: 4 total, 4 passed, 0 failed` (before the single-lane site was wired) | `Results: 4 total, 2 passed, 2 failed`, policy messages name the absolute `_prevention.sdn` |
| runner e2e, directory target (main dispatch, `[route] mode=interpreter`): `simple test <dir>` holding `policy_dir/guarded_spec.spl` and `no_policy_dir/guarded_spec.spl` | policy spec `4 passed, 0 failed` (before the dispatcher site was wired) | policy spec `2 passed, 2 failed`; no-policy sibling `4 passed, 0 failed` in the same run (restore proven) |

New specs (both GREEN through the runner):
`test/01_unit/lib/std/spec/dir_prevention_spec.spl` — Results: 12 total, 12 passed, 0 failed
(walk order/merge/boundary, backslash paths, cache: two specs in one directory = exactly one walk, parser, loader);
`test/01_unit/lib/std/spec/dir_prevention_policy_runner_spec.spl` — Results: 4 total, 4 passed, 0 failed
(policy applies without per-file declaration; no policy = unchanged; ancestor+nested merge; nested-only).

Collateral, BEFORE -> AFTER (all unchanged):
- `test/01_unit/lib/std/spec/it_block_error_accumulation_spec.spl` — Results: 3 total, 3 passed, 0 failed -> same
- `test/01_unit/app/test_runner_new/runner_files_filters_spec.spl` — Results: 65 total, 65 passed, 0 failed -> same
- `test/01_unit/lib/common/mock_verification_spec.spl` — Results: 27 total, 27 passed, 0 failed -> same
- `test/01_unit/compiler/di/di_lock_spec.spl` — Results: 15 total, 15 passed, 0 failed -> same
- `test/01_unit/app/devhub/adapter_bitbucket_spec.spl` — Results: 76 total, 76 passed, 0 failed -> same

Perf: runner wall on the 4-example fixture, same host, same run batch:
no policy 4s, with policy 3s (noise-level; discovery is a handful of
`file_exists` calls per directory, cached; the hooks cost one `call_count`
per registered mock per example).

Related, same day: `prevention_mock_deferred_arming_impossible_2026-08-07.md`
Defects 1 and 2 re-verified GONE (see its 2026-11-04 note).
