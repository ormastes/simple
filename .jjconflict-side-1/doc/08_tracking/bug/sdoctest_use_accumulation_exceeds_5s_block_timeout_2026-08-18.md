# SDoctest block timeout: `use`-line accumulation makes late blocks in an import-heavy doc unrunnable

- **Filed:** 2026-08-18
- **Lane:** RUNFIX (Markdown fence tests). Runner/config are owned by other lanes — filed, not fixed.
- **Status:** OPEN — 2 doctests left RED in
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
