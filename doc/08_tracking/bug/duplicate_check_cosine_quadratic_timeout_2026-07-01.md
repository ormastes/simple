# Bug: cosine duplicate-check mode times out on large files (O(blocks²))

- **Date:** 2026-07-01
- **Area:** `src/compiler/90.tools/duplicate_check` (cosine mode)
- **Severity:** medium (mode is usable only on small scopes)
- **Status:** open

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
