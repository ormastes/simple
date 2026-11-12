# Phase-2 verification matrix `compiler_cli_build` row fails: deterministic HIR-cache store decode refusals + fixed phase-3 missing-surface victim set

- Status: open (root cause narrowed; codec blob capture in progress)
- Found: 2026-11-12
- Component: bootstrap verification harness + HIR cache store roundtrip
  (`src/compiler/80.driver/driver_hir_cache.spl`,
  `src/lib/nogc_sync_mut/sffi/enum_wire.spl`), possibly independent
  module-surface closure/registry gap
- Host: macOS aarch64, 24 GiB physical, bootstrap worktree
  `/private/tmp/boot-main-20261112`, pinned source `5e217d7fd0e`
- Candidate under test: stage2-admitted pure-Simple compiler
  (`sha256=3a795fed8f12…`, admitted 2026-11-12, whole-program sanity route)

## Observation

The post-admission stage-2 verification matrix (`compiler_cli_build` row,
entry `src/app/cli/_CliMain/main_and_help.spl`, ~2811-file closure, 3122
modules) fails in phase-3 HIR lowering with a FIXED victim set (~89 errors,
byte-identical across two runs with different scheduling):

```
[ERROR] HIR lowering error in src/app/t32_cli/mod.spl: missing module surface for .types
[ERROR] HIR lowering error in src/app/t32_cli/bridge.spl: unresolved name: t32_validate_identifier
[ERROR] HIR lowering error in src/lib/editor/services/md_doc_stats.spl: unresolved type: LineStartTable
... and 75 further phase 3 error(s)
```

All victim surfaces show `phase2:surface:file:commit-done` + `released` in
phase 2, so they were built and dropped from memory; phase 3 cannot reload
them.

## What is NOT the cause

- **Not the BOOT-20 alias-routing family** (`module_surface_types.spl`
  scalar-chain workaround, 2026-10-13): victims are keyed by relative
  sibling names across several directories, not doubled logical keys.
- **Not host OOM / fanout budget**: run A (default 18 GiB tree budget, 2 HIR
  workers, row solo at the refusal window) refused 380/3072 store attempts;
  run B (9 GiB tree budget, 1 worker) refused its first 320/320. The
  phase-3 victim set was byte-identical in both runs. A resource limit
  cannot produce an identical victim set under halved parallelism.

## Evidence: HIR-cache store decode refusals

```
[hir-cache-store] refused reason=decode detail=reader kind=malformed
  detail=enum wire enum allocation failed line=71043/72457 token=0
  module=src/app/cli/cli_helpers.spl; entry not stored
[hir-cache-store] rate attempts=3072 stored=2692 refused=380 io_failed=0   (run A)
[hir-cache-store] rate attempts=320  stored=0     refused=320 io_failed=0   (run B, first window)
```

- The decode detail is byte-identical across runs (`line=71043/72457
  token=0`, same first-refused module) → deterministic, data-dependent.
- Per the store contract ("a cache that cannot store is a slow build, not a
  wrong one", `driver_hir_cache.spl`), a refused module is re-lowered in
  memory and the build stays correct — so store refusals alone do NOT
  explain the phase-3 victims. Expect an INDEPENDENT surface-registry/closure
  gap for the victim set (Oct-09 doc's residual suspect:
  `cold_hir_compiler_publication_v1.spl` shard-index export-drop).
- Error text originates in `enum_wire_restore_nil`
  (`src/lib/nogc_sync_mut/sffi/enum_wire.spl:109`): fires when
  `rt_enum_new(owner as i32, variant as i32, payload)` returns nil or a
  value whose `rt_enum_id`/`rt_enum_discriminant` mismatch the prototype.
  Both nil paths (calloc, immortal-registry registration) and the identity
  round-trip are candidates; capture of the failing blob is in progress via
  `SIMPLE_HIR_CACHE_SELFCHECK=1` +
  `SIMPLE_HIR_CACHE_FAILED_DIAGNOSTIC_DIR` (quarantine writer at
  `driver_hir_cache.spl:842`).

## Related finding: fresh-cache parse-shard SIGSEGV (separate bug)

With `SIMPLE_HIR_CACHE_DIR` pointed at a fresh empty dir, the per-file/whole
-program route's parse shard dies deterministically (`exit=-139`,
`[parse-shard] shard=0/2 … FAILED exit=-139`) immediately after
source_closure; the same command with the default warm cache parses fine
(28 files, 26 cache hits, 2 misses). Filed separately as
`native_build_fresh_hir_cache_dir_parse_shard_segfault_2026-11-12.md`.

## Impact

- `compiler_cli_build` and dependent rows (`compiler_bootstrap_tests`,
  `interpreter_interpreter_tests`, `loader_interpreter_tests` — all
  `UNSUPPORTED: full-cli-artifact-not-built`) fail on this host, blocking
  the stage-2 matrix gate and any `--produce-stage3-receipt` lane (which
  re-runs the same gate).
- Dropped-store entries convert a codec/resource limit into plausible-but
  -wrong compiler diagnostics, pulling diagnosis toward the keying family.

## Fix direction

1. Decode the captured selfcheck blob; fix `enum_wire_restore_nil` /
  the enum wire codec for the failing shape (or make the store's decode
  refusal name owner/variant/arity of the failing enum — one eprint would
  have saved a day).
2. Independently trace why the fixed victim set's surfaces are absent from
  the phase-3 registry despite phase-2 commit-done (shard-index
  export-drop suspect; add a phase-3 startup check listing
  committed-but-unregistered surfaces).
3. `[hir-cache-store] refused … enum allocation failed` should include the
  enum identity (owner/variant/arity) in the first-refusal detail.

## Verification so far

- Run A (default budget): 380/3072 refused; phase-3 victim set S; FAIL.
- Run B (9 GiB tree budget): first-window 320/320 refused; byte-identical
  phase-3 victim set S; FAIL.
- Both runs: `compiler_version` PASS, `test_runner_build` PASS (so the
  candidate binary is broadly functional; the failure is closure-shape
  specific).
- Selfcheck capture probe on the diagnostics.spl closure running
  (2026-11-13).
