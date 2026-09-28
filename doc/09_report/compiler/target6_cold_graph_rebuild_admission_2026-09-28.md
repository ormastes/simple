# Target 6 explicit cold graph rebuild admission (2026-09-28)

## Defect and change

After a source edit, `compiler_entrypoint_admit_v1` refused a stale V2 graph
before checking `SIMPLE_PACKAGE_INDEX_COLD_INIT=1`. That made the documented
explicit cold rebuild impossible once any complete graph had been published.

Admission now distinguishes a matching graph, a stale graph without cold
authorization, a stale graph with explicit cold authorization, and a missing
or binding-only index. The explicit cold path pins the new SCV snapshot but
leaves the prior complete graph at `CURRENT`. It publishes no active graph
digest, clears producer/root/variant warm markers, and sets
`SIMPLE_PACKAGE_INDEX_REBUILD_PENDING=1`. Each new admission first clears that
pending marker, so a failed warm retry cannot reuse pending frozen-path
authority. Normal warm requests still refuse a stale graph.

## Evidence

- A no-stub pure-Simple native unit spec published and read a schema-valid synthetic
  one-module V2 graph, then passed the bound, stale-warm, and explicit-cold
  policy cases: 1 example, 0 failures.
- A separate no-stub native fixture compiled 112 units, 0 failures. In a
  one-source Git worktree, `seed` published a binding and then a schema-valid synthetic V2
  graph. After an unstaged source edit, `stale` reported
  `package-index:stale-graph-rebuild-required` without changing `CURRENT`.
  `cold` admitted the new frozen source, kept the old graph digest, cleared
  warm markers, and returned an empty active-index digest. A warm retry in
  the same process failed and cleared the pending marker. All three fixture
  stages printed `PASS`.
- The final fixture rebuild compiled 2 changed units, reused 110, failed 0;
  its cold stage passed after the pending-marker reset check was added.

## Remaining Target 6 work

This transition does not publish a replacement graph. A complete typed HIR,
TLDR/SMF, and archive producer must commit the new generation after successful
cold compilation. Until then, later warm admission correctly refuses the
stale prior graph. System SPipe, broad entrypoint/daemon/remote-cache cutover,
and matched native time/RSS qualification remain open.
