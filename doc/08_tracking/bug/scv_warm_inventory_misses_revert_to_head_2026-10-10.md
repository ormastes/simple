# SCV warm inventory misses a tracked source revert to HEAD

Status: OPEN. Scope: Item 6 source-event authority and warm admission.

## Reproduction

An earlier diagnostic run temporarily changed `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` and then restored its committed bytes. Its persistent source inventory still held the temporary row (SHA-256 prefix `beb045`, 116672 bytes); the live, committed file had SHA-256 prefix `3e3607`, 116337 bytes. Two Item 5 native compatibility probe launches with the admitted Stage 2 compiler stopped before compilation with `SCV-E-ADMISSION: snapshot-index-drift:src/compiler/80.driver/driver_hir_pipeline_lowering.spl`. A fresh compiler cache did not change that outcome. Receipts: `build/mini_builds/item5_jit_owner_explicit_types_20261010/build.log` and `build/mini_builds/item5_jit_owner_explicit_types_fresh_20261010/build.log`.

The explicit `SIMPLE_SCV_INVENTORY_COLD_INIT=1` run rebuilt source authority. The snapshot's driver and changed type-inference file hashes matched the live files; the probe reached all 1009 HIR modules. Its later HIR type-closure failure is independent of this admission failure. Receipt: `build/mini_builds/item5_jit_owner_explicit_types_cold_20261010/build.log`.

## Suspected boundary and required fix

The warm path can return its unchanged inventory when Git and filesystem event batches are empty (`src/app/compiler_entrypoint/inventory_events.spl`, around line 752). A restored tracked file has no net Git working-tree difference from HEAD; in this reproduction no event advanced the stored inventory row. The exact missing event producer remains to be isolated. Do not silently trust a stale row or turn every warm acquisition into a full source scan.

Add a deterministic regression that publishes an inventory for a modified tracked source, restores its HEAD bytes, and then performs warm acquisition. It must either produce an authoritative event and publish the restored row, or reject with an actionable refresh instruction before snapshot admission. Preserve the no-event startup and RSS budgets. Until repaired, explicit cold init is the supported recovery for this recorded case; native warm correctness and Item 6 performance qualification remain open.
