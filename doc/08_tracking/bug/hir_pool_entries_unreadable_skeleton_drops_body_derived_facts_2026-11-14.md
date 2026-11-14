# HIR pool entries unreadable by MIR workers: the surface skeleton drops body-derived function facts

- **Status:** Fixed in source (branch `work/mir-shard-hir-cache-reuse-20261114`); not yet measured on a
  rebuilt compiler (needs a Stage 2 built from this source)
- **Date:** 2026-11-14
- **Area:** two-pass shard route, HIR cache key (`80.driver/cache/module_surface_skeleton_v1.spl`,
  `80.driver/driver_hir_cache.spl`), parser implicit-static promotion (`10.frontend/core/parser_decls_use.spl`)

## Symptom
Bootstrap run 31, Stage 3 build of `src/app/cli/bootstrap_main.spl` (1664 modules,
`SIMPLE_NATIVE_BUILD_THREADS=2`, `SIMPLE_FILE_WORKERS=0`, cranelift, aarch64 Linux, source `5fc681dfd668`):

1. The HIR pool finishes clean: `[hir-shard] completed_workers=2 failed_workers=0 failed_modules=0
   unfinished=0 peak_live_workers=1/2`. Its ledger holds 1664 claims, all `CACHE_STORED`. On the resumed
   run the pool itself reuses its own entries (`cached=1359` of 1664).
2. `[mir-shard] shards=1 parallel=1` then starts one worker, which prints
   `[hir-cache] closure-key=interface surfaces=1664 content_fallbacks=0` and runs `phase=hir` over all
   1664 modules with `cached=0`: from `elapsed_ms=236193` to `1447803`, i.e. **1211.6 s (20.2 min,
   0.73 s/module)** of HIR lowering repeated seconds after the pool stored every module. Its store
   counter climbs with it (`[hir-cache-store] rate attempts=896 stored=896 refused=0`).

## What the MIR worker does
It consults the cache, on the same path as the pool, and misses on the key. Retained route,
`lower_and_check_retained_owner_impl`: `hir_cache_key(...)` at `driver_hir_pipeline_lowering.spl:2111`,
`hir_cache_load_parsed_v1` at `:2115`; `cached` is `hir_cache_hits()`. Nothing is loaded and miscounted.

Evidence that the key, not the header or the load, differs:
- The cache directory holds two entries per module under different names: 1664 written by the pool and
  one more for each module the MIR worker lowered (2753 `.parser-v4.hir` files when 1089 had been redone).
  A header or checksum rejection would rewrite the same file name.
- The pool's key reproduces offline from the ledger. With the closure digest in line 1 of
  `hir/queue-<pid>-0/inventory` (`bca5c36b...9934`), `hir_cache_key` for
  `src/compiler/80.driver/driver_admitted_epoch.spl` gives exactly the stored `5b9c9a9b...d98f`
  (`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`, `SIMPLE_STAGE3_STREAMING_SURFACES=0`,
  `native-target=aarch64-unknown-linux-gnu`, no library mode). No combination of the env switches,
  target part or entry flag (5832 tried) turns that closure digest into the MIR worker's key for the
  same module, and the values that reproduce the pool's key are the ones in the MIR worker's own
  environment (`/proc/<pid>/environ`). The **closure digest** is what differs.
- The 1089 entry pairs are the same HIR: equal line counts, and every differing line is numeric (spans
  of imported declarations). `parse_shard_queue.spl`: 14 of 9161 lines differ (checksum, parser binding
  and four spans; `dir_list_or_empty` is `28605..28942` from the full source, `19715..19913` from the
  skeleton text).

## Cause
`hir_cache_closure_digest` (`driver_hir_cache.spl:224`) folds one row per frozen surface. Since
`da7494c0ebf` (2026-11-13) a row carries the surface's semantic interface digest instead of the file's
content hash.

A HIR shard worker does not parse sources in phase 2. On the retained route
`parse_full_frontend_selected_v1` (`driver_source_parse_selected.spl:170`) parses
`driver_surface_parse_text_v1`, i.e. `module_surface_skeleton_v1(source)`: every non-generic function
body replaced by `pass_do_nothing`. MIR shard workers and the final worker parse the full source. The
route is sound only while `parse(skeleton)` and `parse(source)` build equal surfaces.

One fact of a method's surface is read from its body **text**. `parse_class_body_method_typed`
(`parser_decls_use.spl:640-663`, added by `919c847db73`, 2026-10-25) promotes
`fn new|create|default|from_*` without a receiver to a static method only when the body never mentions
the word `self`. On a skeleton no body mentions `self`, so every such method is promoted.

In this closure exactly one method is affected: `fn create() -> i64:` at
`src/lib/nogc_async_mut/io/platform_event.spl:236`, whose body reads `self._backend`. Instance method
in the MIR worker, static in the HIR pool. That one surface row moved the closure digest, and the
closure digest is folded into all 1664 keys.

Measured on the run's own artifacts (seed interpreter): the skeleton the pool parsed for that module
(the `surface` section of its `.tldr` companion) has canonical surface digest != the full-parse digest
the same companion records in `surface-digest`; the full source parsed by the seed reproduces the
recorded digest. The other 1663 skeletons of the closure, checked the same way, are all equal: it is the only module.

Before 2026-11-13 the rows were byte-keyed, so the keys agreed and the pool's entries were served, even
though the pool had been lowering against a surface where `create` is static since the promotion landed
(2026-10-25). The interface key turned that silent difference into a 100% miss.

## Is it deliberate
No. `module_surface_skeleton_v1.spl` states the equality rule, `worker_surface_differential_spec` pins
it on sample files, and `native_build_main.spl` says the pool exists so that "the real build's HIR
phase is all hits too". Nothing documents a reason for the MIR worker to lower again. The HIR pool has
no other consumer: with the keys apart, its whole output is dead weight.

## Fix
`module_surface_skeleton_v1` now keeps the two function facts the parser derives from a body:
- a blanked body that mentioned the word `self` (the parser's own rule: identifier boundaries, code,
  comment or string) gets the stub `pass_do_nothing  # self`, so the promotion decides as on the source;
- a body holding a contract clause (`in:`, `requires:`, `invariant:`, `ensures:`, `decreases:`,
  `out(r):`, `out_err(e):`, `proof uses:`) is kept verbatim. Contracts are body statements retained on
  the function and folded into the surface projection. No module of this closure has one; the gap was
  found by probe and is the same defect.

The key is not touched: no identity check is weakened, and a hit still requires equal surfaces. Lines
still never move. The `.tldr` companion header (7 -> 8) and the worker surface sidecar header (v2 -> v3)
are bumped so a skeleton stored by an older compiler is never read back.

Spec `test/01_unit/compiler/80.driver/hir_worker_closure_digest_parity_spec.spl` (seed):
red 3/9 before the fix, green 9/9 after. It pins skeleton/full surface equality for a self-using
`create`, a comment-only mention, `in:` and `out(r):` clauses; that a body without `self` stays static
and unmarked; that the worker's closure digest equals the consumer's on a frozen registry; and that the
worker's digest still moves when the method really becomes static (before the fix it did not).

On the real module: the fixed skeleton of `platform_event.spl` changes 9 stub lines (496/496 lines kept)
and its surface digest equals the recorded full-parse digest.

Cost of the extra body pass, old vs new builder on three real files (seed, host load ~24, three rounds
each): 2932 lines 372-619 ms vs 537-624 ms; 1533 lines 155-348 ms vs 177-399 ms; 496 lines 58-81 ms vs
65 ms. Within the noise of the host, at most about +12% of a step that is a small part of a worker's
phase 2. Skeleton size grows by 8-72 bytes on these files.

Other specs after the change (seed): `hir_worker_skeleton_retained_route_spec` 3/3,
`driver_hir_worker_surface_v1_spec` 8/8, `hir_cache_interface_closure_key_spec` 8/8,
`module_surface_skeleton_multibyte_spec` 1/1, `module_artifacts_v1_spec` 7/7,
`worker_surface_differential_spec` 10/11 (the one failure is a `{value}` interpolation error in the
spec's own string at line 96, not touched here).

## What a hit serves after the fix
The same HIR as a fresh lowering, except for byte offsets of IMPORTED declarations. A HIR worker lowers
a claimed module from its full source, but the spans it copies from other modules' surfaces are measured
in the skeleton text: line and column are the source's, `start`/`end` and the span length are not. In a
sample of 300 of the 1089 entry pairs, 52 are byte-identical after the header and the rest differ only in
such triples (`start`, `end`, `end - start`), 860 lines per entry on average, 15011 in `driver.spl`.

This is not new and not widened here: it is how pool entries were served until 2026-11-13, and spans are
the documented exclusion of the interface key (`da7494c0ebf`: "an importer's cached HIR can carry stale
line numbers for a dependency's declarations"). Removing it needs a skeleton that preserves byte
offsets as well as lines (blank a body to equal-length whitespace), which is a format change of its own.

## Expected saving
The MIR shard worker's 20.2 min HIR phase becomes 1664 cache decodes. A hit was measured at up to
~196 ms before the single-decode fix (2026-10-19), so at most ~5 min and likely much less: roughly
15-19 min per MIR shard worker per Stage 3 build on this host, times the worker count when
`parallel > 1`, plus the second copy of every HIR entry (1664 files, about 1.3 GB here). The final
worker links from the ledger and lowers nothing, so it is unaffected. Not measured: this lane may not
run `native-build`.

## Found next to it, not fixed here
1. **Streaming route placeholders.** `driver_worker_surface_closure_v1.spl` gives a worker an empty-text
   placeholder surface for modules outside its seed closure and states that the closure digest is
   unchanged because identity fields come from the source. That held for byte rows only. An empty
   module has a cacheable semantic digest, so the row differs from the real one with
   `content_fallbacks=0` (probe on a 3-module frozen registry: full `0d8e2ee2...`, with one placeholder
   `499f5837...`). Workers with different seed slices would then also disagree at
   `hir_shard_inventory`. Run 31 uses the retained route (`SIMPLE_STAGE3_STREAMING_SURFACES=0`), which
   builds no placeholders. Needs a design decision: the worker cannot compute the real digest of a module
   it did not parse; the per-module `surface-digest` already stored in the `.tldr` companion is the
   obvious source.
2. **`.tldr` section lengths are code points, read as bytes.** `module_tldr_sections_render_v1`
   (`module_tldr_sections_v1.spl:113`) writes `body.len()`; `module_tldr_sections_parse_v1` slices with
   `substring` (bytes). A section holding any multibyte character does not round-trip (probe: 21 code
   points / 25 bytes, `consumed=-1`), so the companion of every such source is rejected: 577 of the
   1664 sources here. Fails closed; the cost is that those companions are never usable.
3. `test/01_unit/compiler/driver/module_surface_skeleton_v1_spec.spl` does not parse under the current
   seed (`Unterminated f-string`, line 49), so it could not be run for this change.
