# Bootstrap snapshot memory retention

Status: source fix under verification; no bootstrap or performance PASS yet.

The Windows hello7 process tree exceeded its 6,835,937 KiB cap before the
final worker. Peak was 6,836,856 KiB; the last external sample separated
2,168,168,448 bytes in the parent from 4,534,685,696 bytes in its HIR child.
The attempt produced no executable. Existing artifacts remain preserved in
`D:/dev/bootstrap-phase2-selective-windows/hello7/`.

## Confirmed source causes

The coordinator refreshed the entire cold source inventory but exported only
its generation. Without a snapshot root, the HIR child acquired authority
and repeated the cold refresh while the parent remained resident. Separately,
cold snapshot materialization read and converted each source several times
for content, chunk, destination and drift verification without releasing
per-file scratch. Neither finding establishes the exact fraction of RSS
attributable to that path; measurements must validate the combined fix.

## Change and invariants

- The parent acquires and publishes complete authority once. All children
  inherit the same snapshot, inventory digest and generation.
- Warm artifact preparation validates inherited authority even with explicit
  source and entry arguments. Advancing CURRENT cannot rebind that authority.
- Snapshot materialization owns one scratch scope per file and promotes only
  a newly allocated result containing the row, reason and drift flag. It ends
  the scope before appending to the retained inventory. Promotion never walks
  the accumulated inventory, avoiding quadratic work.
- Source selectors, byte-packed writes, digest checks, drift checks, atomic
  publication, process isolation and the 7 GB guard remain intact.
- Existing immutable snapshots keep their reuse path. No additional source
  scan or hash is introduced; the redundant inventory refresh is removed.

## Acceptance and performance requirements

1. Native allocation regression: retained live objects after repeated scoped
   materialization are less than half the unscoped control. UTF-8 and CRLF
   bytes, digests, retained rows and refusal reasons remain equal. An error
   must close its scope before a subsequent successful materialization.
2. Authority regressions: canonical selectors match worker policy; explicit
   warm requests retain the old pinned generation after CURRENT advances;
   missing binding data is rejected.
3. Rebuild only the reviewed Simple patch over a new checkout of frozen 5831,
   keeping runtime dependency tree identities and the Phase1 seed pinned.
   Private producer-bound caches prevent mixed-generation writes.
4. The new Phase2 must compile and execute hello under the same 7 GB cap and
   1200-second timeout. Record aggregate/parent/child RSS, elapsed time, cache
   hits and exact producer/source identities. The old run failed around
   826 seconds; it is a failure baseline, not a completed timing benchmark.
5. After cold success, run one warm comparison. Check that the snapshot and
   compilation caches are reused and that no extra refresh or materialization
   was introduced. Report measured timings; do not infer a speedup from code.
6. Run applicable core/lib/MCP checks and native smoke before release landing.
   A Phase2 link alone does not satisfy these or admit Phase3/4.

Tests: `test/01_unit/lib/scv/compile_snapshot_reclamation_spec.spl`,
`test/01_unit/app/cli/native_build_authority_source_roots_spec.spl`, and
`test/01_unit/app/compiler_entrypoint/source_authority_spec.spl`.
The native SSpec and cold/warm bootstrap checks are currently UNRUN.
