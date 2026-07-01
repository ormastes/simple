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

`refine_groups_with_similarity` / the pairwise loop in
`_Detector/similarity_grouping.spl` compares every candidate block against every
other block. Block count grows with file size, so comparisons grow
quadratically, and the interpreter-bound cosine path cannot keep up.

## Not caused by

The 2026-07-01 semantic cross-dir fix (commit "fix: duplication infra …") only
touched `semantic.spl`'s local path; the cosine path (`features.spl`,
`_Detector/*`, `math_utils.spl`) is unchanged. This is a pre-existing trait.

## Fix direction (not yet done)

Bucket cosine candidates before the pairwise step — reuse the same
signature-token inverted-index idea now used in `run_semantic_analysis_local`
(compare only blocks that share a top-weighted token), and/or cap per-bucket
size. That turns the dominant cost from O(n²) to near-linear for the common
case. Token mode (the fast exact gate) is unaffected and remains the default
lexical path.
