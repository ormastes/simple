# Smux release sync source integration review - 2026-10-25

Status: **WARN / NOT_RUN**. No concrete P0/P1/P2 merge-regression finding in the six admitted overlapping paths. This is source integration evidence, not compiler, runtime, provider, cache-hit, or system-suite qualification. No compiler/build/test/native process was launched for this review.

## Revision and scope

- Worktree: `D:/dev/simple-coremux-shared-20261025`.
- Before: `e14abc1968d99b5e511d9326d1e8f8073886133e` (`work/coremux-owners-pre-sync-20261025`).
- Shared comparison base: `932cdf97e3e67476bf338b9797a5e6abfb17fdd1`.
- Upstream target: `3fafd89481dc07d1688e16150e0ca60ea0905825`.
- Reviewed rebased head: `a007a05292906ec5ecf07fa912d64c93a26d4a5f`.
- Scope: exactly the six overlapping paths recorded in `build/review/upstream-sync/admission.sdn`. The root-owned path admission reports 143445 expected paths; this review does not rerun or substitute for that admission.

The table records Git blob IDs, independent of checkout newline conversion.

| Path | Before blob | Upstream blob | Rebased blob |
|---|---|---|---|
| `src/app/cli/native_build_main.spl` | `361158e4028389850f79a28bd0bb1d75dfed11af` | `0c9e2b3dbb0f443af0f378d56cdb929928a0c911` | `d962ff6eb1cb40ab9fa782dc493fda74ad79f708` |
| `src/compiler/80.driver/driver_hir_cache.spl` | `a0b05d9d4064f1b825cf75e78e6ddfacb5ef615c` | `4ede1e0fb4cc23ac3b84f5911be7d7317293bd39` | `384aea17a018cf68a6acc872843841a83481e4bc` |
| `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` | `0cf9e684e1b9d4c0b6e2e7979213a4b791837942` | `b0c2824435287a783bb468299e16854537cd0323` | `7f6dba359fe0a72e9a6cca319aea07516c3d625a` |
| `src/compiler/80.driver/driver_source_pipeline_parsing.spl` | `cf15365c435cfdeb21e74d309c9da6032b176275` | `e87c52816ff7fc68d734c02f7f5265d77bb6fd28` | `6621aac181a7fed4d8ec8b09837b48f96f1283ac` |
| `src/lib/nogc_sync_mut/compression/gzip/inflate.spl` | `578fa70fcc0ae28c86e55625100cb0cf4873a800` | `8e8a2d1e2c8349b0886b3363b3a65da5cfc67737` | `fdd8c379633ab723b868f583dce6a93127580402` |
| `test/01_unit/lib/nogc_sync_mut/compression/gzip_inflate_negative_offset_guard_spec.spl` | `da1a5dc2228fe2fc7640e3f31189dddf031ce95e` | `5ae7f1eccb37264df1dfa7c6bfb895019adb3255` | `13af0f7826bb82319c52853be0085ab1e7a12027` |

## Compiler overlaps

For each of the first four files, the ordered removed/added line sequences for base-to-upstream are identical to those for before-to-rebased (line positions excluded). The complete before/after and upstream/after diffs were inspected. Thus the automatic merge retains the prior configuration edits and applies the upstream edits without dropping or altering either edit sequence in these files.

- `native_build_main.spl`: the semantic `--library-mode` help row, `library_mode_parse_args_v1(args)` error branch, and `library_policy.mode` argument to parse-closure publication remain. Upstream commit-headroom sampling, per-producer peak retention, spawn admission, child dataset cap installation/restoration, and helper imports are retained. Those resource changes do not replace the configured mode or select a library family from a directory.
- `driver_hir_cache.spl`: key/header/parser-binding and load/store/has routes retain explicit default-empty request mode. Empty mode returns the original legacy key/header bytes; configured mode adds the mode-specific hash/header binding. Owned-scope load and store forward that same mode. The upstream failed-shard surface-counter diagnostic is added without altering these identities or cache acceptance checks.
- `driver_hir_pipeline_lowering.spl`: actual, streaming, bootstrap, ordinary and compatibility lowerers still receive `ctx.options.library_mode`; archive selection, parser binding, key/load/store calls and module-surface construction still carry it. Both upstream warning-drain additions remain after replay, guarded by `transient_array_scope_state_v1() == 0`; neither changes the requested mode or cache key.
- `driver_source_pipeline_parsing.spl`: both retained/entry `ModuleSurfaceBuilder.new(...)` sites retain the requested mode. Upstream imports `worker_surface_counters_v1` and emits surfaces-ready diagnostics before lowering. Frozen-surface ownership assignment remains intact.

This is a bounded preservation check, not a new whole-compiler configuration audit. The prior configured-library review and its unexecuted fresh/warm/interleaved-mode scenarios remain applicable; real cache isolation and producer support still require execution with an admitted compiler/runtime.

## Intentional upstream revert

The six paths changed by `87a79148d419261a7f02d785f0abe65eba344ae7` were checked only for exact upstream/rebased blob equality; all six match. These are collateral preservation checks, not additional semantic review scope: `hir_codec_support.spl`, `hir_subst/body_subst.spl`, `_MirLoweringExpr/expr_dispatch.spl`, `backend/backend_api.spl`, `backend/backend_helpers.spl`, and `nogc_async_mut/io/driver.spl`. No qualified-variant, optional-tuple-array or SFFI-unit workaround from the deliberate revert was resurrected by this rebase. Equality proves retention of current upstream content, not that the old producer can compile it.

## Gzip resolution and callers

Upstream `f3b3d615124128de0535deb1645263380a2796cf` intentionally replaces the old heterogeneous result array with `DeflateBlockResult?`. That API supersedes the earlier `[Any]?` source repair. The integrated declaration is `(data: [u8]?, offset: i64) -> DeflateBlockResult?`: `Some(bytes)` binds concrete input before indexing, while nil returns nil. The four values remain `block_type: i64`, `is_final: bool`, `data: [u8]`, and `next_offset: i64`. Both stored and marker results preserve upstream typed constructors; no parallel compatibility API was introduced.

A bounded tracked-source/test caller search finds the synchronous declaration, the asynchronous reexport (including `DeflateBlockResult`), and the two gzip specs. Current RFC callers use named fields and retain nil input. The focused spec also uses named fields, retains three meaningful cases, and adds upstream's extreme-negative-offset control. It covers absent/empty/out-of-range/truncated input, offset-1 stored payload bytes 0/128/255 with next offset 9, and fixed/dynamic marker values. Unexpected nil on a success path takes an explicit failing assertion. No current caller in that inventory expects mixed-array indexing.

Legacy NLEN validation and reserved-block policy are unchanged and outside this resolution. Historical reports/pins are preserved and receive an appended reconciliation note rather than being rewritten as evidence for the new representation.

## Remaining admission

All three focused gzip cases, the existing RFC suite, configured owner/value and fresh/warm/interleaved-mode controls, compiler integration, and application/system scenarios remain **NOT_RUN** here. No runtime pass or new failure count is inferred from source or Git checks. Actual execution still requires a genuine admitted Phase 3 compiler, matching runtime/provider, exact current source/command receipts, and the root-owned finite resource/cycle authorization. This review does not authorize a retry or a Phase 2 rebuild.
