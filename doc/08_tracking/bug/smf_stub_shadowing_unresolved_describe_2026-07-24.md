# Stale untracked `.smf` stubs shadow real modules → every spec fails `unresolved name: describe`

**Date:** 2026-07-24 · **Severity:** critical (tooling) · **Status:** mitigated (quarantine), root fix open

## Symptom

Every SSpec file, on every available binary, fails instantly with
`HIR lowering error: unresolved name: describe` (also `it`, `expect`,
`context`) plus `[parser_error] ... unexpected token in expression: ':'`
(kind 161) on `describe "...":` lines. Looks exactly like a runner/deploy
clobber or a std.spec regression. `simple test` reports whole-file FAILs;
delegation reports `seed sibling not found`.

## Root cause

The working tree contained **~9,046 stale `*.smf` files** (uniform 179-byte
stubs, dated 2026-02-25) under `src/` and `test/`, e.g.
`src/lib/nogc_sync_mut/spec.smf` next to `spec.spl`. Module resolution
prefers the `.smf` over the `.spl`, so `std.spec` (and many other `std.*`
modules) resolved to an **empty stub** — `describe`/`it`/`expect` genuinely
did not exist in the resolved module. None of these files are git-tracked
(`git ls-files '*.smf'` = 0); clean worktrees have zero and their runners
work, which is the discriminating check.

Related, previously-filed layers of the same incident:
`native_cli_run_std_hardware_brace_import_unresolved_2026-07-24.md` (deploy
left compile-only frontend; missing `simple_seed` sibling) and the dynSMF
fail-open history (`std.spec` SMF shadowing, 2026-07-17).

## Diagnosis recipe

1. `find src test -name '*.smf' | wc -l` — any nonzero count of untracked
   `.smf` in a source tree is suspect; compare against a known-good worktree.
2. Discriminator: the same spec run from a clean worktree cwd behaves
   differently (module resolution follows the cwd source tree).

## Mitigation (applied)

Quarantine all untracked `.smf` under `src/` and `test/` (move out of the
tree; they are build artifacts). After removal the same binaries run specs
normally — devhub suite verified 25 files / 517 examples / 0 failures.

## Open root fixes

- Resolver should reject/ignore stub `.smf` whose payload is empty or older
  than the sibling `.spl` (fail-open guard exists for dynSMF; extend to
  module resolution).
- Builds should not emit `.smf` into `src/`/`test/`; artifacts belong under
  `build/` (native_cache). Whatever produced the Feb-25 sweep is unidentified.
