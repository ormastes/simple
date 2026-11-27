# Worker surface table escapes its parser lease

This document records the initial repair and its then-pending qualification. Its repeated full-class/bloom promotion strategy is superseded by the [second-lease owner repair and native RED/GREEN evidence](worker_surface_second_lease_raw_root_promotion_2026-10-30.md). The final owner retains the class once and promotes only the mutable entries dictionary on later leases.

Status: concrete ownership defect; relation to import failure unproven.
Source repair and native lifetime qualification are pending.

The selected streaming parser begins a transient lease, then calls
worker_surface_text_v1. That call initializes the process-global TldrTableV1
and publishes newly allocated digest/skeleton strings into it. The retained
frontend owner boundary paused and promoted parser/cache/surface roots but
omitted this table. Lease end could reclaim a live process-local cache owner.

The failed02c9 runner build and successfula2f29 build retained identical
shard_mem_clamp skeleton bytes and equivalent provider HIR declarations after
root-prefix normalization. Failure occurred only in another worker importing
the provider, with302 cache restores versus37 in a successful worker. This
correlation does not establish that the table lifetime caused the import miss.
Detailed retained comparison: /tmp/runner-import-audit-20261030.md and
/tmp/phase2-worker-import-divergence-20261030.md. Caches remain preserved.

## Ownership contract

The cache belongs to one worker process. No cross-thread/process mutable
sharing, pointer transport or layout change is introduced. Source text is a
scoped input; published keys and surfaces become retained owned output. The
small worker_surface_table_owner_v1 module owns the TldrTableV1 root and dirty
state. Lookup/publication preserve set-once cache semantics. Creation or a new
publication marks the graph dirty; only successful promotion clears it.

The existing paused retained-frontend hook promotes this root even when a
frontend cache restore skipped parser initialization. Repeated promotion must
walk a persistent table's new children: entries, requested map, fill queue and
IdScope/bloom belong to the retained class graph. The runtime's existing graph
walker supports permanent containers with newly scoped children; no pointer
cast or scalar success substitutes for the native check below. Promotion
failure propagates through the existing parse failure path.

## Focused evidence plan

The native worker_surface_table_lifetime fixture calls the production small
owner API, avoiding a full compiler import closure. It publishesA in one lease,
retains/closes, churns allocations, publishesB in a second lease, retains/closes,
then checksA+B. A same-class graph check verifies dictionary, queue and IdScope
fields after close/churn, proving more than a boolean promotion return.
Optional omission control must fail or be explicitly reported as not reproduced;
it never counts as a positive test. No source/table evidence is synthetic.

The repair retains the existing full graph rather than guessing ownership of
individual backing arrays. Walking a growing table for each publication can
add quadratic entry traversal (including a65,536-element bloom). Measure the
next managed run; no RSS or speed improvement claim is made. Full CLI resource
qualification and actual daemon-routed plain/SSpec execution remain separate.
