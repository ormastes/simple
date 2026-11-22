# dupcheck cosine: Pass 0 makes within-file results depend on scan scope

- **Status:** verification-pending
- **Component:** `src/compiler/90.tools/duplicate_check/_Detector/similarity_grouping.spl`
  (`collect_cheap_line_window_candidates`, `scan_duplicate_blocks`)
- **Found:** 2026-11-22, during runtime C de-duplication (PRs #10677, #10680, #10681, #10685)

## Symptom

`--include-c --mode cosine` gives different within-file groups for the same
file depending on which other files are scanned with it. Both seed and native
binaries behave the same (no seed/native mismatch).

| input | groups naming `runtime_db.c` |
|---|---|
| dir with only `src/runtime/runtime_db.c` | 0 |
| dir with all 82 top-level `src/runtime/*.c` | 16 (all intra-file pairs) |

`runtime_process_owned.c` alone: 0 groups; in the full runtime dir: 83 report
lines name it.

## Cause

Pass 0 keeps a file only if some identifier-normalized `min_lines` line window
occurs more than once across the whole scan. Cosine pairs are fuzzy: two
near-duplicate blocks inside one file usually share no exactly equal
normalized window, so the lone file is pruned before Pass 2. In a bigger scan
the same file survives because one of its windows happens to match a window in
another file; then Pass 2 extracts all its blocks and finds the intra-file
pairs. Pass 0 is a recall-lossy prefilter whose loss depends on the scan set.

## Expected

A file's intra-file cosine groups should not depend on unrelated files in the
scan. Options: key Pass 0 on a shorter window or a signature-token set that is
a true superset of cosine candidates; or document Pass 0 as lossy and offer
`--no-pass0` for single-file audits.

## Repro

```
mkdir a && cp src/runtime/runtime_db.c a/
dupcheck a --include-c --mode cosine -q            # Found 0
mkdir b && cp src/runtime/*.c b/ && rm -f b/miniaudio*
dupcheck b --include-c --mode cosine -q | grep runtime_db.c   # 16 groups
```

## Fix (2026-11-22, verification-pending)

`collect_cheap_line_window_candidates` now admits a file by either rule:

1. **intra-file** — an identifier-normalized single signal line occurs twice
   in the file. Decided by the file alone, so intra-file groups no longer
   depend on the rest of the scan. Two >= 0.85-cosine `min_lines` blocks share
   at least one structurally equal line in practice; an exact `min_lines`
   window usually does not.
2. **cross-file** — unchanged `min_lines` normalized window shared with another
   file.

Evidence (seed `bin/simple.exe run .../main.spl DIR --include-c --mode cosine`):

| input | before | after |
|---|---|---|
| only `runtime_db.c` | 0 groups | 7 groups |
| 82 `src/runtime/*.c` (rt3) | 250 groups, 41 files kept, 564 s, 2269 MB | 270 groups, 53 files kept, 812 s (1.44x), 2243 MB |

Spec: `detector_grouping_spec.spl` "keeps fuzzy intra-file cosine groups when
the file is scanned alone" fails before (12/13), passes after; whole
`test/01_unit/app/duplicate_check/` 96/96 after. Native checker not rebuilt.
