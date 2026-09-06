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

## Follow-up findings + fixes landed (same day)

- **Producer identified and fixed** (`d12c7be42b7`): the test runner's
  native/compile mode wrote its `.smf` compile artifact BESIDE the source
  (`file_path.replace(".spl",".smf")`) and deleted it only on clean
  completion — any interrupt (timeout kill, OOM, Ctrl-C) orphaned a stub.
  Artifact now goes under the temp dir.
- **Cache trust guarded**: `run_test_file_smf` treated *any* existing `.smf`
  sibling as precompiled cache and executed it directly. Now gated by
  `_smf_artifact_is_usable` — rejects missing, stub-sized (<256 bytes), or
  stale (older than the sibling `.spl`) artifacts.
- **Resolution-order claim corrected**: a dedicated investigation could NOT
  reproduce ".smf preferred over .spl" in any current resolver — every .spl
  resolver ignores `.smf` entirely, and the Rust seed's
  `module_resolver/resolution.rs` checks `.spl` BEFORE `.smf` in the same
  directory. A planted stub beside `spec.spl` did not break current binaries.
  The historical mechanism for the incident-era binaries (Jul-22/Jul-24
  builds; cf. the Jul-17 "std.spec SMF shadowing = Rust-layer defect" note)
  remains unpinned — but with the producer dead, the cache gated, and current
  resolvers proven .spl-first, the class is closed at every reachable layer.
