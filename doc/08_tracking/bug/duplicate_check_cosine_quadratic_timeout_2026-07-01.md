# Bug: cosine duplicate-check mode times out on large files (O(blocks²))

- **Date:** 2026-07-01
- **Area:** `src/compiler/90.tools/duplicate_check` (cosine mode)
- **Severity:** medium (mode is usable only on small scopes)
- **Status:** fixed (2026-07-04, task #89)

## Resolution (2026-07-04)

The bug-report repro now completes: 22-file tool directory, `--mode cosine
--min-tokens 30 --min-lines 6 --max-allowed 999` → 34 groups, exit 0, 7m20s
wall (interpreter). Before: killed, never completed. Fixes, in
`_Detector/similarity_grouping.spl` / `_Detector/interner_and_logging.spl`:

- Removed the `dada8d28f79b` workaround that silently aliased cosine mode to
  the exact-hash line-window path (it computed zero cosine similarity;
  `refine_groups_with_similarity` was dead code). Real pipeline restored.
- Fixed a hidden O(n²) in `collect_token_window_candidates` /
  `collect_hash_counts_in_file`: `end_idx` reset to `i+window_size` per outer
  token instead of carrying forward (two-pointer). O(tokens) amortized now.
- Extraction volume: cosine no longer zeroes `repeated_hashes` to scan every
  file. New Pass 0 prunes files via an identifier-normalized line-window
  inverted index (structure key: identifier runs → `#`, digit runs → `0`),
  so renamed-identifier clones still anchor. An exact-hash pre-filter (this
  report's original suggestion) is NOT usable: it prunes exactly the fuzzy
  pairs cosine exists to find (caught by detector_grouping_spec).
- Pairwise comparison: signature-token inverted index (same technique as
  semantic.spl's local path) + real `cosine_similarity` within buckets,
  replacing the capped O(n²) loop with its token-count approximation.
  Oversized-bucket skips and block sampling are logged, never silent.
- JIT unblocking (interpreter fallback was the per-token cost multiplier):
  renamed `val vec` shadows (ollama_client.spl, semantic.spl) and replaced
  deprecated `import std.env.*` module-alias calls in env config/validation
  (both families) — each was an HIR "Unknown variable" lowering failure.

### Residual (still open, separate concerns)

- Interpreter tokenize() is ~2ms/token; 7m20s for 22 files is completion,
  not speed. Next JIT blocker: W1006 "mutation without mut capability"
  lowering `get_tokens_cached` (cache.spl mutates `manager.cache` through a
  parameter) — capability-model issue, needs its own fix.
- Something on the dev box SIGTERMs processes matching `simple run` at
  ~63–66s wall (pattern-based sweep; the same binary copied to another name
  runs 7m+ undisturbed). Long-running verification must use a renamed
  binary copy or `bin/simple test`.
- Pre-existing spec failures (verified unchanged with this fix fully
  reverted, so not regressions from it): `cache_spec.spl` — 4 examples fail
  with "Cache: 0 files, 0 tokens" (token-cache mutation through the
  `TokenCacheManager` parameter not visible to the spec's manager in the
  `it`-block context), and `phase1_integration_spec.spl` — "reuses the
  token cache across repeated scans" fails with the same signature. Same
  probable root as the W1006 mut-capability note above.

## Symptom

`bin/simple duplicate-check <dir> --mode cosine` is killed (SIGTERM / timeout)
on directories with medium-to-large `.spl` files. A single 200-line file yields
~800 candidate blocks; the pairwise comparison is O(blocks²), so a 22-file tool
directory never completes under the default run limits.

Reproduce:

```bash
bin/simple run src/compiler/90.tools/duplicate_check/main.spl \
    src/compiler/90.tools/duplicate_check --mode cosine \
    --min-tokens 30 --min-lines 6 --max-allowed 999
# -> "Starting pairwise comparison of N blocks..." then Terminated (143)
```

Small scopes finish fine (2 short files → 320 blocks → 4776 comparisons → 0
groups in <30s), so the logic is correct; only the scaling is the problem.

## Root cause

Not the pairwise loop — that is already bounded in
`build_similarity_adjacency` (`max_total_comparisons = 7000`,
`max_comparisons_per_block = 36`, and `sample_blocks_for_similarity` caps
analyzed blocks at 320).

The blow-up is upstream, in block extraction. `scan_duplicate_blocks` special-
cases cosine (`similarity_grouping.spl:271-273`): it sets
`candidate_files = files` and `repeated_hashes = {}`, so
`find_duplicates_in_file_with_hash_filter` runs with an empty hash filter and
emits *every* sliding-window block from *every* file (≈800 blocks from two
short files). Pass 2 extraction and `group_exact_blocks` over that unfiltered
block set — interpreter-bound — is what SIGTERMs on a medium directory before
sampling/pairwise even begins.

## Not caused by

The 2026-07-01 semantic cross-dir fix (commit "fix: duplication infra …") only
touched `semantic.spl`'s local path; the cosine path (`features.spl`,
`_Detector/*`, `math_utils.spl`) is unchanged. This is a pre-existing trait.

## Fix direction (not yet done)

Cap the extracted-block set for cosine the way the pairwise step is already
capped. Options, cheapest first:
- keep a hash pre-filter for cosine too (don't zero out `repeated_hashes`),
  scanning only files/blocks that already collide, OR
- apply `sample_blocks_for_similarity`'s 320-block cap (or a per-file block cap)
  *before* Pass 2 extraction, not just before the pairwise loop.

Not a mechanical reuse of the semantic inverted-index fix — that fix is in the
`semantic.spl` doc path; this is a different code path (lexical block
extraction). Token mode (the fast exact line-window gate) is unaffected and
remains the default lexical path.
