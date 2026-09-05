# Compiled checker full-tree diagnostics — 2026-08-02

## Corrected result

Compiled checker SHA-256
`27b9593a697d7115b9e16b4471b33f969bd98229e410a866c2ef28d3d95c6874`
checked a content-addressed snapshot of 11,433 files from `src/compiler`,
`src/app`, and `src/lib`.

- 11,019 files pass.
- 414 files fail when run individually.
- 250 of those 414 are checker false positives: 247 pure-Simple parser
  capability/parity gaps, two raw-text concurrency lint matches, and one
  checker-entry argv collision.
- 147 are invalid source files.
- 17 are intentional SSpec command-block/check-surface rejections.
- The 414 files map to 40 disjoint routing categories: 20 checker/parser and
  20 source/layout categories.

The exhaustive evidence is under
`build/mini_builds/full-tree-compiled-check-bounded-cycle1/`:
`manifest.tsv`, `file-results.jsonl`, `routing-manifest.jsonl`,
`routing-summary.json`, and per-invocation logs.  The committed compact routing
manifest is
`doc/03_plan/compiler/bootstrap/compiled_checker_failure_routes_2026-08-02.tsv`.

## Explicit retraction: no batch-state leak proved

An intermediate analysis incorrectly called 6,690 isolated passes
"batch-state false positives" merely because their aggregate batch exited
nonzero.  That inference is retracted.  A nonzero batch proves only that at
least one member failed.

The minimal pair is:

1. `src/app/audit/ffi_usage.spl` alone: exit 0.
2. `src/app/audit/ffi_analyzer.spl` alone: exit 1.
3. analyzer followed by usage in one process: exit 1, with the correct summary
   `1 error(s) found in 1 of 2 file(s)` and no diagnostic for the follower.

Evidence is retained in
`build/mini_builds/full-tree-compiled-check-bounded-cycle1/minimal-pair/`.
Therefore no parser-reset/state-leak bug was filed.

## Highest-impact unowned routes

1. `pure_parser_type_or_multiline_signature_gap`: 62 files.  Reference,
   function, empty-array/capability types and multiline signatures accepted by
   the canonical parser are rejected by the compiled pure parser.
2. `pure_parser_class_member_gap`: 51 files.  Keyword-named fields and public
   or otherwise canonical class members are rejected in class bodies.
3. `source_foreign_import_syntax`: 43 files.  Primarily the app interpreter
   subtree uses Python-style `from .. import` source and requires a source-owner
   conversion lane, not a parser workaround.

The next checker routes are metadata blocks (24), unmatched parser surface
(20, medium confidence), keyword identifiers (18), and structured/keyword
exports (17).  The routing TSV gives exact counts, confidence, evidence, and
owner surface for all categories.

## Snapshot caveat

The earlier unbounded xargs run saw 13,957 paths while concurrent worktree
changes were active.  Its PTY capture is partial.  The durable bounded manifest
contains 11,433 digest-verified files and is the only scope used for exact
per-file totals.  No claim is made that it covers paths removed before manifest
creation.

