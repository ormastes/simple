# Unit child admission scans the whole closure (2026-11-15)

Status: verification-pending (partial)

Every per-file unit child ran `worker_admitted_edges_v1` over the full inventory, at one resolution per source, to compute a pick order that every unit shares. That made each unit O(closure) before it emitted its first object.

The fix sits behind `SIMPLE_UNIT_ORDER_INDEX=1`, which is off by default. The first unit publishes `<hir_queue>/unit_order.idx` and later units decode it. The spec `test/01_unit/compiler/driver/unit_order_index_spec.spl` shows 0 resolutions per unit at both N=20 and N=400, compared with N when the switch is off.

Still open:
- phase 1 still reads every source file, and the TLDR-freshness skip is not implemented;
- the advice scan covers all contents;
- the pick stats ledger files for every entry that is already taken.

No wall-time or RSS numbers have been measured, and no native off-identity check has been run, because no heavy build was allowed while phase 3 was running.
