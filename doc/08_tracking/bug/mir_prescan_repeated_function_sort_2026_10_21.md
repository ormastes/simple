# MIR function prescan repeatedly sorts the same module inventory

Status: source defect confirmed; isolated source candidate; runtime UNRUN.
Registration: pending authoritative bug/dedup queue access; no bug ID assigned.
This is a distinct prescan performance defect, outside the closed parallel-MIR
feature repair count. It is not established as the cause of the live object
build delay or as a regression introduced by the selective-MIR candidate.

Baseline: commit `6ea0bd7fa6cb86f3c1abdbd0852fdc5d4eaaa777`, tree
`fc99a0f5038663c1db0ded30166d0bd698d92c27`. The live producer view was read
only. Candidate source is isolated in
`/home/yoon/dev/simple-prescan-inventory-perf-20261021`.

In baseline `_MirLowering/module_lowering.spl:1871–1879`, the function
prescan calls `hir_fn_scalars_in_v1` once for each of F functions. That
accessor invokes `hir_fn_scalars_p_v1`, which materializes all dictionary
keys, stable-sorts them, and scans from the beginning to the requested row.
The existing sorter is a bottom-up merge sort, so ordering takes
O(F² log F) total work and selection visits F(F+1)/2 prefix elements.

The candidate freezes the ordered original SymbolId handles once per module
prescan invocation, then reads the same nine fields by direct indexed key
expressions in a tiny parameter-only codec helper. It preserves missing
module, invalid-position and nil-row fallbacks, stable tie order, and the
existing scalar feeder. It adds no global cache, owner field, explicit clone,
key reconstruction, HirModule binding or HirFunction binding in production.
The old extractor remains as a compatibility API and differential oracle.

Actual-owner regression fixtures are in
`test/01_unit/compiler/hir/hir_prescan_function_inventory_spec.spl`.
Detailed mutation/order/lifetime proof and source work counts are in
`doc/09_report/mir_prescan_function_inventory_source_review_2026_10_21.md`.

No elapsed-time, RSS, native ABI or object-completion improvement is claimed.
The admitted runtime/build scheduler must qualify the candidate, including
array-handle argument transport and original-key lifetime, before acceptance.
