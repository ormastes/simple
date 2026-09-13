# TestDaemon cache drops the `output` field across save/load

**Status:** OPEN (unverified 2026-09-12)

- Date: 2026-08-27
- Found via: sspec modernization residual wave, batch resid7_part_00
- Reproducing spec: `test/01_unit/app/test_daemon/test_daemon_cache_module_spec.spl`
  ("persists cached output across save and load") — RED: `expected  to equal
  line one\nline two` (entry.output is empty after reload).

## Defect

`src/app/test_cache_shared.spl`:
- `shared_cache_save` (line 87) serializes only
  `test_path|dep_hash|result_status|passed|failed|skipped|duration_ms` —
  `output` and `cached_at` are never written.
- `shared_cache_load_entries` (line 97) therefore reloads every entry with
  `output: ""`.

The daemon cache round-trip silently loses the captured test output text.

Secondary staleness (fixed in the same pass): the spec referenced the old
field name `result_output`; the struct has been `output` since the rename
(the spec did not even compile — `semantic: class TestCacheEntry has no
field named result_output`).

## Unblock / fix

Persist `output` (and `cached_at`) in the cache line format — escape or
encode the `|` and newline characters in `output` (e.g. base64 or a `\n`
escape) since the format is line-based and `|`-delimited, then decode on
load. Bump `TEST_RESULT_CACHE_VERSION` so old caches invalidate.

Neighbor to add when fixing: a spec asserting an output containing `|` and
newlines survives the round-trip (the delimiter-collision case), per the
"every fix ships two specs" rule.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
