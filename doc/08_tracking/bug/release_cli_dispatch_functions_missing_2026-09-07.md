# `simple release` dispatch calls 20 functions that exist nowhere

- **Found:** 2026-09-07, cutting `1.0.1-beta.1` from `origin/main` @ `1bd13da6125`.
- **Status:** OPEN. Blocks every documented release subcommand except `plan`
  and the GitHub-release options.

## Symptom

```
$ bin/simple run src/app/release/main.spl version-check
error[E1002]: function `run_version_check` not found
  = help: check the function name or import the module that defines it
```

## What is actually wrong

`src/app/release/main.spl` (254 lines) imports only
`app.release.github.{create_github_release, default_repo, default_token,
read_body_file}`. Its `match subcommand:` block at `:199-254` then dispatches to
`run_version_check`, `run_version_render_plan`, `run_version_bump_plan`,
`run_version_bump`, `run_session_register`, `run_session_status`,
`run_session_cleanup_check`, `run_session_close`, `run_beta_prepare`,
`run_backport_check`, `run_convergence_discover`, `run_convergence_receipt`,
`run_convergence_admission`, `run_self_review_plan`, `run_candidate_check`,
`run_candidate_create`, `run_candidate_status`, `run_candidate_admit`,
`run_support_check`, `run_promote_check`, `run_withdraw_check`.

`grep -rn 'run_version_check' src/` returns exactly two hits: this call site,
and an unrelated private `_run_version_check` in `src/app/ui/build.spl`. Not one
of the twenty-one wrappers is defined or imported anywhere in the tree.

The underlying logic is present and correct — `check_repository_version` in
`src/app/release/version_authority.spl:268`, plus `prepare.spl`,
`session_authority.spl`, `candidate_authority.spl`, `convergence.spl`,
`support_policy.spl`. Only the CLI wrapper layer that `main.spl` calls is
missing, so this is a lost adapter layer, not lost logic. Last touching commit
is the `e274cd33719` share-history worktree merge.

## Impact on this release

`.claude/skills/release.md` names `simple release version-check` /
`beta-prepare` / `candidate-check` / `promote-check` as the validation
commands; none of them run. The `1.0.1-beta.1` projection bump was therefore
validated by calling `check_repository_version(".")` directly from a throwaway
driver, which reports:

```
version-check: PASS semver=1.0.1-beta.1 channel=beta projections=17
```

That is the same predicate `version-check` would have evaluated, but it is not
the documented command, and it covers only the version authority — the session,
candidate, and promotion gates have no reachable entry point at all.

## Second finding, exposed by the same check

The four registry projections were **already stale before this release**:
`tools/{mcp,lsp-mcp}-registry/{package,server}.json` sat at `0.9.9` while
`release/version.sdn` said `1.0.0-rc.1`. They are declared in
`_required_projection_paths()` (`version_authority.spl:82-95`), so
`check_repository_version` returned `valid: false` with reason "declared release
version projections are missing, ambiguous, or stale" on unmodified
`origin/main`. Fixed here by projecting `1.0.1-beta.1` into all four. It went
unnoticed for exactly as long as the command that would have caught it has been
unreachable.

## Fix

Restore the wrapper layer in `src/app/release/main.spl`: import the authority
modules and implement the twenty-one `run_*` functions as arg-parse + call +
render. Add one runnable check that dispatches every advertised subcommand and
asserts none of them errors with E1002, so the layer cannot silently disappear
again.

## Triage 2026-11-13 (P3 tools lane, work/p3-tools-20261113, base origin/release/1.0.0)

The missing adapter layer is **restored in tree**: all 21 `run_*` wrappers the
record lists exist in `src/app/release/main.spl` (verified by grep; the help
listing at `main.spl:124` advertises every subcommand), so the E1002 dispatch
defect itself is fixed on this branch.

Verifying the repro end-to-end with the session binary (`bin/simple.exe`, Rust
seed from the main checkout) surfaced one further blocker in the same entry
closure, now fixed: `src/app/release/self_review_policy.spl:212` (`_json_int`)
did `if item == nil: missing else: item as i64` on a `json_to_number` result
(`any?`), which the current compiler rejects (nil-only-in-unsafe ERR-01 /
E-OPT-CAST-001, `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:1243`).
The manual nil guard did not count as narrowing; the whole `release` entry
closure refused to lower (JIT and interpreter alike), so no subcommand could
run at all.

Fix: rewrote `_json_int` to `match json_to_number(...): case Some(n): n as i64;
case nil: missing` — the `match` narrowing form both compilers accept.

Before -> after:
- before: `bin/simple run src/app/release/main.spl version-check` died in HIR
  lowering (ERR-01 optional cast); no subcommand reachable.
- after: the CLI runs end to end; `version-check` reaches the version
  authority and answers with its verdict (on this branch:
  `status=rejected, reason="product, semver, line, or channel is invalid"` —
  `release/version.sdn` declares `semver: 1.0.0-rc.1` with `channel: beta`,
  which `check_version_channel` (`src/app/release/policy.spl:213`) rejects as
  an rc/beta mismatch. That mismatch exists identically on origin/main and is
  release metadata policy, not a dispatch defect, so it was not changed here).
- canary `test/02_integration/app/context_log_modes_spec.spl`: 4/4 PASS.
