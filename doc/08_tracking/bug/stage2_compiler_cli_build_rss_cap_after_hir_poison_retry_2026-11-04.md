# Stage 2 `compiler_cli_build` rss-cap-exceeded: HIR poison then in-process retry (2026-11-04)

Status: **fix-implemented-verification-pending** (needs a sanctioned bootstrap rerun, s2d).

## Evidence (s2c, `/private/tmp/boot2-out/s2c`, macOS M4 24 GiB)
`stage2-compiler-tests/aarch64-apple-darwin/verification/logs/compiler_cli_build.log`:

1. Lines 13-43013: HIR pass #1 lowered **all 3020** modules in-process and stayed
   under the 12 GiB tree cap, then `[collect-all] 4 module(s) poisoned` ->
   `phase 3 FAILED`. Deterministic compile errors, not memory.
2. Line 43045: `[mir-shard] ... falling back to in-process unsharded MIR` -> the
   driver restarted load/parse/HIR **in the same process**.
3. Pass #2 hit `peak_rss_kib=13348288` at HIR 1665/3020 -> `rss-cap-exceeded`.

So the RSS kill is a consequence; the root cause is the poison.

## Root causes fixed
- `src/app/traceability/snapshot/git_provider.spl:158,172` used
  `"...^{commit}"`; `{commit}` is interpolation -> `unresolved name: commit`.
  Escaped as `^\{commit\}` (same idiom as `submodule_git_adapter.spl`).
  Verified with the s2c Stage 2 `compile`: 7 -> 0 `unresolved name: commit`.
- `materialize_imported_owner_parameter_dependencies`
  (`module_reexport_materialization.spl`) reported an imported owner's
  `where K: Eq + Ord` as `unresolved imported owner type parameter dependency`.
  `Eq`/`Ord` have no library declaration; local where-bound lowering
  (`types.spl` builtin bound arm) already treats
  Clone/Copy/Debug/Default/Drop/Eq/Ord as ambient. The check now does the same
  (only when the name still resolves nowhere). Poisoned `adaptive_map`,
  `adaptive_set`, `sprof_collection_profile`. Compiler change: verified only by
  the next Stage 2 rebuild.

## Remaining (not fixed here)
- After fixing HIR, the single-module `compile` of `git_provider.spl` reaches
  MIR and fails: `indirect callable lacks a proven function signature`
  (`switch_operators_calls.spl:9073`). May also hit the full-CLI build.
- In-process retry after a deterministic HIR failure re-lowers everything
  without releasing pass #1 state (retained across passes): it should fail
  fast instead of retrying when the shard failed on compile errors.
- `SHARD_TREE_HEADROOM_KB_V1` (24 GiB default) >= host RAM on a 24 GiB Mac, so
  the HIR worker pool is always 0 (`effective 0 kB`) and HIR runs in the
  coordinator. Not touched (reserve policy is owner-controlled).
- HIR cache store `refused=363 reason=decode ... enum allocation failed`:
  separate codec defect, not causal.
