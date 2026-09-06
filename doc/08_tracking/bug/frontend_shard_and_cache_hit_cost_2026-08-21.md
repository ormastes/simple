# Front-end parse cache: a HIT cost seconds, and shard receipts hid it

- **Date:** 2026-08-21
- **Status:** FIXED (front-end cache decode path, shard receipt attribution)
- **Area:** `src/compiler/10.frontend` (flat-AST pool codec, front-end cache),
  `src/compiler/80.driver` (parse phase receipts), `src/app/cli` (parse sharding)
- **Related:** `doc/08_tracking/bug/native_build_frontend_not_incremental_2026-08-21.md`

## Symptom

Two numbers off a `native-build` of the `src/app` bootstrap closure looked
irreconcilable:

- run7 (`--threads 8`): 8 parse-shard workers took roughly 870 s of wall for
  666 files, about 80 files each in about 600 s — ~7.5 s per file.
- a single-worker run (`jitabi3/stage1b.log`) reported
  `[build] parse 667/667 +118076ms` — 0.18 s per file, ~40x faster per file.

The obvious reading was that shard children had fallen off the JIT path the
single worker was on. That reading is wrong, and the log could not disprove it,
which is the second half of this bug.

## What was actually happening

### 1. The comparison was hits versus misses, not JIT versus interpret

Both processes run in the same mode. `run_native_build_worker`
(`src/app/cli/native_build_main.spl`) sets `SIMPLE_EXECUTION_MODE=interpret`
when unset and publishes `SIMPLE_BINARY` **before** it calls `run_parse_shards`
(same file, a couple of dozen lines later), and `rt_process_spawn_async` passes
the parent environment through. A shard child therefore runs in exactly the
mode the main worker runs in. There is no shard-specific de-JIT.

The single-worker run was fast because it was replaying a warm front-end cache:
its own shards report `[frontend-cache] hits=73 misses=0 parses=0`. So the
comparison was a cache HIT path (0.18 s/file) against a cache MISS path
(7.5 s/file) — a real parse under the tree-walking interpreter, which is the
known cost of that path and not a regression.

### 2. The real defect: a cache HIT cost seconds, not milliseconds

A hit restores 151 flat-AST pools from a line-oriented text blob and runs the
existing bridge. It should cost tens of milliseconds. In run7's main worker it
cost about 1.2 s per module, and in the single-worker run individual hits hit
3.7 s (`dt=3676ms` on `src/compiler/mir/mir_aop_injection.spl`).

The dominant term is `flat_pool_unescape`
(`src/compiler/10.frontend/core/flat_pool_codec.spl`), called once per stored
**text pool entry** — the largest population in the blob. It took a
one-character slice `value[i:i+1]` and rebuilt an accumulator `out = out + ch`
for **every character of every value**, in interpreted Simple. Two things were
wrong with that:

- The codec emits a backslash only as the lead byte of `\\` or `\n`, so a value
  containing no backslash at all decodes to **itself**. The overwhelming
  majority of pool entries (identifiers, type names, spans-as-text) are in that
  class and were paying the full per-character walk for nothing.
- Even for values that do carry an escape, a per-character interpreted loop is
  the wrong shape when the runtime has bulk `replace`.

The store side had the mirror problem: every encoder accumulated
`out = out + piece` in a loop.

### 3. Why the log could not settle it

The driver emitted the per-file "in-flight" receipt **before** the shard
ownership test (`driver_source_pipeline_parsing.spl`). Each of 8 shard children
therefore claimed all 666 files as `current` while parsing only its own ~83:
8x666 receipts of which 8x583 named a file that process never opened, and the
`dt` stamp on those lines measured the gap between two skips. Merged into one
log with the main worker, the per-shard per-file cost was simply not
recoverable — which is exactly why the JIT hypothesis survived as long as it
did. Measured over `fp7/stage1_build.log`: 7335 `parse` receipts with a median
`dt` of 1 ms, for a phase that took ~870 s.

There was also no instrumentation on the hit path at all: the miss path had
`SIMPLE_PARSE_PHASE_PROFILE=1` timing, the hit path had none, so even a
correctly attributed receipt could only say "this hit took N seconds", never
which of decode, restore or bridge spent them.

### Refuted: "shards re-parse because only the driver reads the cache"

Raised against run8, where every shard reported `parses=73..94` (about the
whole file list once summed) while the merged log showed `parse 666/666` with
`dt=1-3ms` per line. Both observations have a different cause:

- **Shards do consult the cache.** An isolated warm shard measured here reports
  `[frontend-cache] hits=94 misses=0 parses=0` and `[parse-shard] done
  shard=0/8 parses=0`. An earlier real 8-shard run reports `hits=73/85/90
  misses=0 parses=0` per shard. Structurally, the lookup lives in
  `frontend_parse_or_restore` (`src/compiler/10.frontend/frontend.spl`) — the
  single boundary every parse goes through — and nothing about it is
  conditional on the shard spec. Pinned by
  `test/01_unit/compiler/driver/parse_shard_execution_mode_spec.spl`.
- **run8's shards missed because its scope was cold**, not because they
  bypassed anything: a run under a fresh `SIMPLE_CACHE_SCOPE` gets a fresh
  cache DIRECTORY, so its first pass misses everything by construction, and any
  compiler-source edit rotates the scope key as well (see below).
- **The `dt=1-3ms` lines are not cache hits.** They are the skip receipts each
  shard emitted for the ~583 files it does not own — defect 3 above. That is
  precisely why the log read as "666 files, all instant, 20 minutes of wall".

### Still open (not this change)

- **Per-shard startup.** Each of 8 children loads the whole interpreted
  compiler closure before parsing anything (~3.6 GB RSS per process observed).
  That preamble is paid 8 times and is a real floor on the sharded path.
- **Tail imbalance.** Ownership is a static hash split with no work stealing,
  so the phase ends when the unluckiest shard ends: run8 had shards 0-4 done
  while 5-7 still ran, with 6 cores idle. A dynamic work queue would fix it.
- **Decode is still 69% of a hit** (773 ms of 1137 ms). The per-line array
  operations in `flat_pool_dec_*` are the remaining term; a length-prefixed
  binary codec, or simply not running the worker under the tree-walking
  interpreter, is what would move it.
- **Skip sharding when the cache is already warm.** With hits cheap (this
  change) a warm build gains nothing from 8 extra processes and pays 8
  preambles.

## Fixes

All semantics-preserving; the stored blob format is unchanged, so entries
written before the fix are still readable after it.

1. `flat_pool_unescape` — three tiers computing the identical result:
   identity when the value has no backslash; three bulk runtime `replace`s
   (hide `\\`, decode `\n`, restore) when it does; the original
   character-at-a-time loop as a fallback if the value happens to contain the
   sentinel, so the fast path can never be the reason a value decodes wrongly.
2. Encoders (`flat_pool_enc_i64/bool/text` and the three list encoders) build a
   parts array joined once instead of a growing accumulator.
3. `build_module_from_flat_pool_blob` emits a `PARSEHIT` line under the
   existing `SIMPLE_PARSE_PHASE_PROFILE=1` gate, splitting init / restore /
   bridge / total plus blob size, so a slow hit names its own sub-step.
4. `frontend_parse_cache_store` counts successful stores
   (`frontend_parse_cache_stores()`), so a module written twice in one process
   is visible rather than merely slow.
5. The parse loop decides shard ownership **before** emitting the in-flight
   receipt, so a shard child's log names only files it actually parses.

## Mechanism tests

- `test/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.spl` — a
  cost gate on decode. Verified discriminating: against the pre-fix codec both
  cost cases FAIL (`3 examples, 2 failures`); with the fix all three PASS. The
  third case is a fidelity case that passes in both, so the gate is a cost gate
  and not a behaviour change. Bounds are an order of magnitude above the idle
  cost because this host is shared.
- `test/01_unit/compiler/driver/parse_shard_execution_mode_spec.spl` — pins the
  spawn-after-env_set ordering that makes a shard child run in the main
  worker's mode, and the ownership-before-receipt ordering. Verified
  discriminating: reverting the driver change turns the receipt case RED.
- `test/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.spl` (existing)
  stays green, and `scripts/check/check-flat-ast-codec-complete.shs` reports
  `PASS — 165 pool(s) checked`.

## Measurement

Probe: one shard worker (`--parse-shard=0/8`) over the real `src/app`
entry closure (666 sources), `--threads 1`, run twice against a private cache
scope — pass 1 cold (its ~83 owned files are real parses), pass 2 warm (the
same files are all hits). Pre and post run concurrently from two detached
worktrees at the same commit (`096e9adbc4f`), so they share the host's load.

All numbers from one shard worker (`--parse-shard=0/8`, 94 owned modules of
666, `--threads 1`) over the `src/app` entry closure, pre and post run from two
detached worktrees at the same commit `096e9adbc4f` against the same deployed
seed. Shared, heavily loaded host (load ~35).

| | pre | post | |
|---|---|---|---|
| cold pass wall (94 real parses) | 1063 s | 1066 s | unchanged, as intended |
| warm pass wall (94 hits, `hits=94 misses=0 parses=0` both) | 320 s | **217 s** | -32% |
| warm parse-phase span (build timer) | 170.3 s | **106.9 s** | -37% |
| cost per cache hit | 1812 ms | **1137 ms** | -37% |
| parse receipts emitted by the shard | 761 | **189** | 573 skip receipts gone |

Post-fix hit breakdown, from the new `PARSEHIT` line (94 hits, avg blob 63 KB):
`init 128 ms / restore 773 ms / bridge 218 ms`. So decode is still 69% of a
hit. The escape-free fast path removed the per-character work on the majority
of pool entries; what remains is the rest of the codec walking roughly 20k blob
lines with a few interpreted array operations each, at ~39 us per line. This
change does not claim to have made a hit cheap — it made it 1.6x cheaper and,
for the first time, measurable. The next lever is a bulk/binary codec or a
non-interpreted worker; both are larger than this fix and are recorded below.

### Measuring this at all requires a FROZEN tree

The front-end cache scope is
`native_build_cache_scope_key(..., native_build_compiler_identity())`, and
`native_build_compiler_identity()`
(`src/compiler/80.driver/driver_build/incremental.spl:168`) folds
`native_build_compiler_source_fingerprint()` — a fingerprint of the compiler's
own sources. Editing ANY compiler source therefore invalidates every stored
entry, by design and correctly. A first attempt at the post measurement edited
the tree between the cold and warm passes and the warm pass reported
`hits=0 misses=94`: it was a second cold pass, not a hit replay. The numbers
above come from a re-run over a tree frozen for the whole probe.

## Not fixed here

The MISS path is still an interpreted parse at several seconds per file. That
is the cost of running the worker under the tree-walking interpreter and is
tracked separately; sharding exists precisely to spread it across processes,
and it is a pure optimisation (a failed shard just means the main build parses
those modules itself).

The seven top-level dump functions (`flat_stmt_pools_dump` and its siblings in
`core/ast_stmt.spl`, `core/_Ast/decl_nodes.spl`, `core/types.spl`,
`core/_AstExpr/nodes.spl`) still accumulate `out = out + <sub-blob>` across
~165 pools, so each store copies the whole growing multi-megabyte blob once per
pool. That is quadratic in the number of pools and is worth fixing, but it is
deliberately NOT in this change: those `out = out +` lines are the exact text
`scripts/check/check-flat-ast-codec-complete.shs` derives the pool list from,
so rewriting them has to be done together with that guard rather than
opportunistically alongside a hit-path fix. It is a store-path (cache MISS)
cost only and does not affect a hit.
