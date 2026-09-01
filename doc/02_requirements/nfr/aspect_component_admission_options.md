<!-- codex-research -->
# NFR options: checked aspect-component admission

## Target 1 — Balanced transactional admission

- Resolution is O(manifest entries), with no full-tree scan or child process.
- Static selection performs zero artifact opens.
- Dynamic startup performs at most one checked pack open and one checked catalog
  read for the selected component; repeated acquisition uses resident indexes.
- Size/digest/interface/implementation identity is checked before publication.
- Failure publishes no partial loader, catalog, binding, or generation state.
- Unknown/off/corrupt/stale/digest-mismatch/capability-denied cases fail closed.
- Startup lazy I/O remains forbidden after operational publication.
- Measurement fixture: 128 manifest entries, one selected 64-module pack, and a
  1 MiB encoded catalog on the retained x86_64 baseline host and runtime hash.
- Across at least five fresh-process samples, report p50/p95 and max RSS. Target
  warm selected-component admission p95 <= 5 ms, incremental max RSS <= 8 MiB,
  and resident catalog/index storage <= 2x encoded catalog bytes + 1 MiB.
- Counters must prove zero static opens, dynamic pack opens <= 1, catalog reads
  <= 1, full-tree scans = 0, and child processes = 0.
- Validate size/digest again from the opened bytes immediately before atomic
  publication; a post-open mutation/swap sabotage must leave state unchanged.

Pros: satisfies the security/performance gates in
`doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md`.
Cons: requires explicit transaction/rollback and biting negative controls.
Effort: M.

## Target 2 — Tight transactional admission

- Same correctness, fail-closed, atomic-publication, counter, five-sample, and
  post-open mutation requirements as Target 1.
- Same 128-entry/64-module/1 MiB fixture.
- Warm admission p95 <= 2 ms, incremental max RSS <= 4 MiB, and resident
  catalog/index storage <= encoded catalog bytes + 512 KiB.

Pros: stronger startup and memory budget for latency-sensitive deployments.
Cons: may require compact indexing, fewer copies, and more platform-specific
measurement stabilization before acceptance.
Effort: L.
