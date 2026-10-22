# MIR feed identity must include the actual ordered owners

Status: source repair authored; executable regression and repaired-producer bootstrap admission pending.

Remote cycle-126 (`bf3ce38b521`) preserves the initial `hir_modules.values()` feed when the physical source indices are `[0, 1, ...]` and its length matches. Those indices describe the admitted source inventory, not dictionary iteration. For inventory owners `[app.a, app.b]` and an existing feed `[app.b, app.a]`, both old conditions hold, yet skipping the rebuild violates `driver_mir_physical_source_indices_v1`'s inventory-order contract.

The driver now collects actual module names directly from the retained context feed and calls `driver_mir_feed_is_identity_v1`. It requires equal complete counts, identity indices, valid bounds and equal nonempty canonical owners at every position. A matching feed remains intact without a dictionary reread or a HirModule value copy. Other feeds follow the existing rebuild path. Work and temporary owner storage are linear in module count.

Six new scenarios in `test/01_unit/compiler/driver/mir_physical_owners_spec.spl` call the actual production predicate: matching order, reversed same-size feed, missing/extra owners, filtered inventories, reordered/duplicate/invalid indices, and canonical aliases versus empty/wrong owners. They contain 14 explicit assertions. These tests have not run: the helper's existing module_lowering dependency brings in the compiler closure, and the available new Stage 2 candidate failed admission. No copied predicate or old-producer run is counted as validation.

This repair does not fix the separately observed nil function values in the rejected frozen producer or the remote cycle-126 comment's remaining erased dictionary-read defect during nonidentity rebuilds. Required follow-up is actual execution of this regression and the unchanged p2_add admission probe under a repaired producer, followed by filtered/multi-module feed coverage. Preserve the original AV dump, rejected artifact and receipts.
