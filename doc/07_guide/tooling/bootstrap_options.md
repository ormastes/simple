# Bootstrap options, shard knobs and cache protocol state

Dated 2026-10-25, against `release/1.0.0`. Each item names the PR or file it was
checked against. Opt-in means the default is OFF today.

## Stage 3 and the sanctioned script

- The sanctioned bootstrap is `scripts/bootstrap/bootstrap-from-scratch.sh`
  (see `.claude/rules/bootstrap.md`). `bin/simple build bootstrap` is a separate
  seed-side reimplementation, not this path.
- Stage 3 runs from a frozen, admitted Stage 2 (Stage 2 is ADMITTED on
  release/1.0.0, #4260). Do not edit or rebase the frozen tree
  ([frozen worktree](frozen_bootstrap_worktree.md)). A fix that lives in
  compiler source only takes effect after Stage 2 is rebuilt.
- #4498 (9965e560854): the whole-program bootstrap-fixed MIR lane in
  `driver_pipeline_lowering.spl` now prescans all closure structs
  (`prescan_module_struct_names`, mirroring the `--entry-closure` prescan). It
  cured 479 "array return record element has no unique provider layout" errors
  on the 1453-module closure. Needs a Stage 2 rebuild to take effect.
- #4499 (merged 2026-10-24): `module_source_relative_path` no longer cuts a
  repo-relative path at an inner `/src/`
  (`src/lib/nogc_sync_mut/src/collections/x.spl` was named `collections.x`).
  Absolute paths still anchor at the first `/src/`. All four naming callers
  (driver, backend, MIR, HIR) share the function.
- Windows link: `src/compiler_rust/runtime/build.rs` links `ws2_32` and
  `mswsock` (IOCP provider, #4430, merged). Windows default lane is llvm-mingw
  UCRT with clang + lld. Never GCC.

## Shard and memory knobs

Policy lives in `scripts/bootstrap/lib/product-frontend-policy.shs` and
`scripts/bootstrap/tests/phase-c-frontend-policy-test.shs`.

| Variable | Meaning / policy default |
|---|---|
| `SIMPLE_SHARD_MEM_CLAMP` | `1` (default); `0` is refused: "unbounded frontend fanout forbidden" |
| `SIMPLE_PARSE_SHARD_MAX` | Max parse-shard workers; the Windows owner pins `1` (one frontend) |
| `SIMPLE_PARSE_SHARD_WORKER_KB` | Per parse worker budget, policy value `1650000` |
| `SIMPLE_HIR_SHARD_WORKER_KB` | Per HIR worker budget, policy value `3000000` |
| `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` | Positive, enforced process-tree limit |
| `SIMPLE_HIR_SHARDING` / `SIMPLE_PARSE_SHARDING` | Switch HIR / parse sharding (`0` disables) |
| `SIMPLE_HIR_WORKER_SKELETON` | Opt-in (`=1`): HIR workers build surfaces from the module skeleton (#4473) |

Stage 3 bisect (2026-10-25): turning skeleton and HIR sharding on or off did
not change the MIR error set, so they are not the cause of those errors.

## HIR cache self-check bug (OPEN)

Frozen-Stage-2 Stage 3 logs 313 `[hir-cache] SELFCHECK FAILED ...
nil_in_non_optional_scalar` lines; the encoder writes a nil token the generated
decoder refuses, so entries are not stored and HIR shard work is recomputed.
See `doc/08_tracking/bug/hir_cache_selfcheck_nil_in_non_optional_scalar_2026-10-25.md`.

## Direction: per-file src to obj (IN PROGRESS, not the default)

The target design is per-file source-to-object jobs
(`doc/05_design/compiler/incremental_build/src_based_tldr_build_v1.md`). Landed
pieces: FileFiber v1 per-file async read with one parse and TLDR publish
(#4453), single-flight leaders (#4441). The whole-program lane above is still
what bootstrap uses.

## Cache protocol (all landed 2026-10-24)

- `.spab` packed pointer-free AST: encoder + validating reader (#4445), hit path
  via mmap view and typed-token restore (#4457), reference table 0x0104 and
  set-once map 0x0900 (#4463). Opt-in with `SIMPLE_FRONTEND_SPAB=1`; the default
  flips only after the whole-closure native gate passes on a Stage 3 binary.
  Design: `packed_binary_ast_v1.md`.
- `DigestV1 { algo_id, hex }` over a hash algorithm registry (#4421):
  `sha256`=1, `blake3`=2, `sha3-256`=3 (collision-resistant); `xxh3-128`,
  `xxh3-64`, `crc32` (fast fingerprints). Up to 3 digests per side are
  negotiated; an unknown algorithm or length mismatch is a MISS, never a match,
  and different algorithms never compare. Macro keys (#4435), generic
  identities (#4433) and persisted build-cache digests (#4481) use it.
- `GuardIdV1` + `ActiveGuardRootV1` (#4412, #4420): guard root is part of the
  AOP directory key.
- Single-flight: leaders get a start time and always complete (#4441).
- Daemon file-queue request loop and usage ledger (#4396); per-source disk and
  memory byte caps (#4405); free-space admission before every publish (#4442);
  reference-aware eviction (#4458).
- Lean formal gate (#4411): `scripts/check/check-cache-protocol-formal.shs` and
  `scripts/check/check-cache-formal-source-binding.shs` (pins sha256 of live
  cache-key declarations; re-pin with `--update` after review). Missing `lake`
  is ERROR exit 2, never PASS. Theorems landed: T-K1/T-I1 (#4415), T-RR1
  (#4447), T-RG1 (#4449), T-EV1 (#4451), T-HA1 (#4452), T-SF1 (#4427).

## Process

- Never `git stash` (shared across worktrees); use your own `work/*` worktree.
- Merge a PR only when `gh pr checks <n> | grep '^Code Idiom'` is green.
- Take host job counts from `~/.config/simple/host.sdn`.
- Never GCC on Windows.
