# SDoctest block timeout: `use`-line accumulation makes late blocks in an import-heavy doc unrunnable

- **Filed:** 2026-08-18
- **Lane:** RUNFIX (Markdown fence tests). Runner/config are owned by other lanes — filed, not fixed.
- **Status:** FIXED 2026-11-03 — `build_accumulated_preambles` (extractor.spl) dedups top-level use/import lines; guard spec `test/01_unit/lib/test_runner/sdoctest_preamble_dedup_spec.spl`. Doc fences in import_quick_reference.md re-verification pending.
  `doc/07_guide/quick_reference/import_quick_reference.md` (fence lines 225 and 247).

## Mechanism

`extract_reusable_lines`
(`src/lib/nogc_sync_mut/test_runner/sdoctest/extractor.spl:228`) hoists every
`use` and `import` line from each block into all *subsequent* blocks of the same
file. Cost therefore grows monotonically down the file, while the per-block
timeout is a flat 5000ms (`default_timeout` in
`src/lib/nogc_sync_mut/test_runner/sdoctest/config.spl`).

In a document whose subject *is* imports, this is quadratic-ish by construction:
every block is a list of `use` lines, so every block makes every later block
slower. Measured on the reconstructed preamble for the block that was at line 53:

```
$ time bin/simple run /tmp/t8.spl      # 15 accumulated use lines
real  0m4.107s
```

4.1s against a 5.0s budget, on a box at load ~29 — and that was only the first
third of the file.

## Evidence it is cost, not content

- Each failing block is reported as `TIMEOUT after 5000ms`, never a parse or
  resolution error.
- The individual snippets run standalone in well under 1s
  (`use app.io.*` alone: 0.82s; `use std.spec.{...}` x3: 0.97s).
- The set of failing blocks **moves between runs at the same content**: before
  the fence cleanup the failures started at line 53; after it, line 239 passed
  and line 225 failed instead. A content defect would not migrate with load.

## Progress already made (documentation-side only)

Reclassifying genuinely non-runnable fences (deliberately-WRONG forms and
placeholder symbols) out of the `simple` language tag removed them from the
accumulation:

| stage | Results |
|---|---|
| baseline | `20 total, 5 passed, 0 failed, 0 skipped, 15 errors` |
| after WRONG-block split | `20 total, 14 passed, 0 failed, 0 skipped, 6 errors` |
| after placeholder fences retagged | `16 total, 14 passed, 0 failed, 0 skipped, 2 errors` |

The last 2 are correct, copyable examples. They are **left red deliberately** —
making them pass would mean deleting valid documentation, and the defect is in
the runner's cost model, not in the doc.

## Suggested fix (for the owning lane)

Any one of:
1. Raise `default_timeout`, or make it scale with the accumulated preamble size.
2. Deduplicate accumulated `use` lines before emitting the block (this file
   re-imports `std.spec` and `app.io` many times over; the hoisted preamble has
   large literal duplication).
3. Do not hoist `use` lines across `##` section boundaries — reference docs are
   organised as independent sections, not as one running program.

Option 2 is likely the cheapest and helps every import-listing document.

## Addendum 2026-11-11 — lane runner5: SUPERSEDED (fix + doc re-verification complete on refreshed seed)

The owning lane took suggested fix 2, exactly as recommended:
`build_accumulated_preambles`
(`src/lib/nogc_sync_mut/test_runner/sdoctest/extractor.spl:519`) now
deduplicates top-level `use`/`import` lines (first-seen order kept) while
accumulating a block's reusable lines into subsequent preambles, so an
import-listing document no longer grows its preamble linearly. Guard spec:
`test/01_unit/lib/test_runner/sdoctest_preamble_dedup_spec.spl`.

Seed-smoke verification on refreshed seed (build-commit 0791c2b7f4a7):

1. `bin/simple.exe test test/01_unit/lib/test_runner/sdoctest_preamble_dedup_spec.spl
   --mode=interpreter --no-cache` → **3/3 PASS**
   (`preamble_build_ms=9` for 40 import-heavy blocks; last preamble carries
   only the 3 unique `use` lines).
2. The status line's pending item — re-verification of the
   `import_quick_reference.md` fences — is now done:
   `bin/simple.exe test --sdoctest doc/07_guide/quick_reference/import_quick_reference.md
   --mode=interpreter --no-cache` → **1 total, 1 passed, 0 failed, 71 ms,
   "All sdoctest blocks passed!"**. The document-side mitigation recorded in
   the bug body has since retagged every import-listing fence out of the
   `simple` language tag (33 fences remain, all `text`/`bash` except one
   runnable `simple` block), so the use-accumulation shape this bug measured
   no longer exists in that document.

Verdict: SUPERSEDED — runner cost model fixed (preamble dedup) and the
reference doc re-verified green on the refreshed seed.
