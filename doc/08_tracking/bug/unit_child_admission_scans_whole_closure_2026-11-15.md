# Unit child admission scans the whole closure (2026-11-15)

Status: verification-pending (default ON in Wave C1; native wall-time/RSS pending)

Every per-file unit child ran `worker_admitted_edges_v1` over the full inventory, at one resolution per source, to compute a pick order that every unit shares. That made each unit O(closure) before it emitted its first object.

Originally behind `SIMPLE_UNIT_ORDER_INDEX=1` (off by default), Wave C1 (2026-11-18) flipped `SIMPLE_UNIT_ORDER_INDEX` to default ON (`0`/`false`/`off` rolls back). The first unit publishes `<hir_queue>/unit_order.idx` and later units decode it. The spec `test/01_unit/compiler/driver/unit_order_index_spec.spl` shows 0 resolutions per unit at both N=20 and N=400, compared with N when the switch is explicitly set to `0`.

Wave C1 (2026-11-18) also resolved the already-taken prefix rescan in `worker_unit_pick_v1` by maintaining an advisory `<hir_queue>/.pick_cursor` under `<hir_queue>/.lock`: each pick scans `[cursor .. order.len())` first, advancing past `.claim`/live `.pick` entries, and wraps around to `[0 .. cursor)` only when `picked.len() < batch` (preserving dead-owner `.pick` reclamation and full-scan `.drained` semantics).

Still open:
- phase 1 still reads every source file; a content-hash skip-fresh of picks is behind `SIMPLE_UNIT_ORDER_SKIP_FRESH=1` (verification-pending, spec `unit_order_skip_fresh_spec.spl`), and the TLDR-freshness skip is not implemented;
- the advice scan covers all contents;
- resolved in Wave C1 (2026-11-18): steady-state picks advance via `.pick_cursor` instead of statting every already-taken prefix entry from `0`.

No wall-time or RSS numbers have been measured, and no native off-identity check has been run, because no heavy build was run in this lane.
