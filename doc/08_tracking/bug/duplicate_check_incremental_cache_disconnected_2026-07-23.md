# Duplicate-check incremental cache is disconnected — 2026-07-23

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Reproduction

The previously deployed CLI accepted `--cache-path` syntactically, then returned
exit 2 with `incremental duplicate detection is not implemented`.

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

## Implemented solution

The grouping owner now imports the incremental processor through the interner
leaf, avoiding the facade cycle. Token and cosine modes share normal grouping;
semantic modes still reject caching. The versioned cache uses UTF-8 byte hex,
content hashes, strict fail-cold parsing, and deleted-file pruning. The
fresh-binary smoke covers uncached/create/reuse/change/delete/`--no-cache`,
cosine parity, exit parity, and JSON stdout purity.

## Remaining evidence

Build one fresh incremental Stage-4 CLI and run the focused phase-2 spec and
bounded essential-tools smoke once. Until both pass, this is source-fixed rather
than release-qualified.
