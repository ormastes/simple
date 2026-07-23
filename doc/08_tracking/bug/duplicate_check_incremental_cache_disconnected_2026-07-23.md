# Duplicate-check incremental cache is disconnected — 2026-07-23

**Status:** OPEN / CANONICAL CLI FAILS CLOSED

## Reproduction

The canonical full CLI accepts `--cache-path` syntactically, then returns exit 2
with `incremental duplicate detection is not implemented`. Configuration with
`use-incremental: true` is rejected the same way.

## Root cause

`incremental.spl` can serialize per-file blocks, but the canonical detector
facade only warns and performs a full scan. The cache processor returns raw
blocks and cannot be substituted for the normal grouped result. Importing it
directly into the detector also creates a cycle because the cache module imports
the detector facade.

The existing Phase 2 “end-to-end” unit scenario calls `find_duplicates`, never
calls `process_files_incremental`, and expects the cache to remain empty. It is
not evidence that the CLI cache works. Deleted-file entries are not pruned by
the current serializer either.

## Required solution

Keep exit 2 until the grouping owner is non-cyclic. Then add one fresh-binary
two-run smoke that proves cache creation and reuse, followed by changed-file and
deleted-file invalidation. Do not append cache statistics to JSON output unless
the schema is intentionally revised.
