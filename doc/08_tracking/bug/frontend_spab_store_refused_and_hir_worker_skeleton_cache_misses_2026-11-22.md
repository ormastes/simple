# Frontend cache: `.spab` store refused for non-entry modules; HIR workers miss on skeleton keys (2026-11-22)

Status: Finding 1 FIXED in source (unverified at runtime, see "Fix"); Finding 2 and HIR adopt OPEN
Binary measured: integ25 Stage 2 (`pinned-c1a10190b978/build/bootstrap-s2probe-integ25`)
Context: MIR fork route (`SIMPLE_MIR_FORK_WORKERS=N`). The root and the 8 HIR shard
workers each spend ~15 min in "parse" (f25: load_sources ends at 0.8 min, parse ends
at 15.9-18.3 min). That is about half of the 33-min critical path.

## Finding 1: HIR workers mostly MISS. They do not hit slowly.

`[frontend-cache]` receipts in `boot-fable-lane-scripts/p4/cli-f25.build.log.saved`:

| process | hits | misses | parses |
|---|---|---|---|
| HIR workers (8) | 1091-2597 | 1540-2444 | 1761-2665 |
| MIR root | 4131 | 6 | 227 |

Each HIR worker parses `module_surface_skeleton_v1(source)`
(`src/compiler/80.driver/driver_hir_worker_surface_v1.spl:25-28`). The frontend
cache key is derived from the parsed text. The parse-fiber warmers
(`driver_parse_shard_entry.spl:283`, `parse_full_frontend_selected_v1(e.content, ...)`)
store keys only for the full source text. So the warmed entries cannot match a
skeleton lookup. The ~1,100-2,600 hits per worker come from earlier worker runs or
from sibling workers.

Most of each worker's 15 min is therefore real skeleton parsing (~2,300 parses).
It is not restore cost.

Fix (2026-11-22): the coordinator (`native_build_main.spl`) now computes the HIR pool
size before spawning parse shards and sets `SIMPLE_PARSE_SHARD_SKELETON=1` on them
only when a HIR pool follows. Each parse-fiber child, after a module is fully done,
parses `driver_hir_worker_skeleton_text_v1(source)` -- the same function the workers
use -- through the same `parse_full_frontend_selected_v1`, which stores it under the
worker key. A skeleton failure only counts `skeleton_failures` in the
`[parse-fibers]` receipt. Key equality is pinned by
`test/01_unit/compiler/driver/driver_hir_worker_surface_v1_spec.spl`. Not covered:
the capsule `--parse-shard` route (`SIMPLE_FILE_FIBERS=0`). Expected effect: worker
parse time falls to the hit cost, which is bounded by Finding 2.

## Finding 2: `.spab` packed store refused for every non-entry module

`frontend_parse_or_restore` (`src/compiler/10.frontend/frontend.spl:120-215`) stores
`.spab` through `frontend_spab_store_v1` and falls back to the text `.fpc` only when
that store is refused. Evidence that the store is refused:

- The f26 cache holds 585 `.spab` files against 7,865 `.fpc` files.
- On a fresh cache, a cold `bug_add` run under strace showed exactly ONE
  `.spab.*.tmp` write, for the entry module. There were 115 successful blob
  captures, all `borrowed=true`.
- Even the 158-byte `src/lib/sffi/cli_args.spl` is refused.

As a result, every warm hit takes the `.fpc` path
(`build_module_from_flat_pool_blob`): about 20 ms of a 29 ms load on small files,
which is ~70% of per-file parse time.

The refusal branch is not identified yet. It is one of the following.

`frontend_spab_store_v1` (`frontend_spab_cache_v1.spl:81-100`) refuses on:
- `trace.len() == 0`, or
- an empty `flat_packed_encode_refs_v1` result.

`flat_packed_encode_refs_v1` (`core/flat_pool_packed_v1.spl:522+`) returns empty on:
- a bad family or shape,
- an id over its limit,
- a walk mismatch.

Leading hypothesis: in the transient-scope capture case,
`_FlatAstBridge/module_assembly.spl:~1940-2000` promotes only `_fab_captured_blob`.
`_fab_captured_trace` and `_fab_captured_refs` are not promoted, so after the first
transient scope they are empty or dangling. The entry module is parsed outside that
path, which would explain why it alone succeeds.

The instrumented probe (eprints on each refusal branch, natively built
`src/app/spabdbg`) could not run: the probe build itself ICE'd in
`lib.common.crypto.word_ops` (hir_lower). The available Rust seeds cannot parse the
current `src/lib` (`unit ByteSize: i64`), so the probe cannot be interpreted either.

## Is `.spab` actually faster? Not established

On the same entry (`bug_add/main.spl`, 6.8 KB), a `.spab` hit measured
load 24 / verify 3 / build 20 ms. The `.fpc` hits averaged ~20 ms build at 11.6 KB.
In f24, worker parse time did not track hit ratio (903 hits -> 1092 s,
2894 hits -> 1198 s).

Before fixing the refusal, run a same-file A/B: `SIMPLE_FRONTEND_SPAB=0` warm twice
on the same entry. Fix the refusal only if `.spab` is at least 2x faster.

## Ruled out

- The O(n) char->byte span-cursor rewind on hits. `e333c37af8f` is not on
  release/1.0.0, but the equivalent per-source prefix table (`221fda0de8f`,
  `lex_span_prefix_ensure`) is already in `c1a10190b97`.
- `SIMPLE_FILE_WORKERS=0`: it only selects the two-pass shard route. The root's
  phase-2 streaming loop (`driver_source_parse_streaming.spl`, calling
  `add_streaming_module_surface` at `driver_source_parse_selected.spl:421`) is
  serial either way.
- Quadratic HIR adopt in the root (`[hir-cache] adopted=4496`, ~12 min). Time is
  flat across quartiles (f24 quartile sums 159/216/224/130 s), so it is
  decode-bound (`hir_cache_load`: read + sha256 + `hir_module_decode` + promote,
  ~160 ms/module, `driver_hir_cache.spl:500-640`).

## Not fixed

`.spab` refusal and HIR adopt: no code change. Both touch the shared parse path, and neither is
measured on a binary that runs the modified source: the stage2 binary only runs
prebuilt code, and the seeds cannot interpret the current tree.
