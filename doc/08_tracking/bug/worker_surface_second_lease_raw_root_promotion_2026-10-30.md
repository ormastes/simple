# Worker surface table rejects its second parser lease

## Failure and exact boundary

`/tmp/simple-phase2-attempt13-cli-memory-diagnostic-cwdguard2-20261030/build.log` completes admitted graph discovery (4469 modules), promotes/releases surface 1 (`main_and_help.spl`), then fails surface 2 (`args_and_os_commands.spl`) with every frontend owner true except `worker_table=false`. The earlier scanned=4352 message is graph discovery, not table cardinality. Peak RSS is below the outer cap. A giant table/depth limit does not explain this second-publication failure.

Admitted producer SHA: 516c26c664452096ec47496ad771d20e121fd9fefc4a300bf549e7803240918c; source 69c0a06e9f31ca1bd22ed7ee171ab0c1cde4d3ab. Disassembly of `TldrTableV1.create` calls `rt_alloc(32)` at 0x1a03050 (target 0x21ff9e8) and tags the returned pointer. It does not call registered `rt_struct_alloc`.

The initial promotion finds that raw root in the current transient registry and retains its graph. `rt_core_reclaim_transient_raw` then clears the registry after reclaiming unpromoted allocations. On the next lease the class remains live, but its raw allocation lacks a persistent size proof. `rt_transient_heap_promote` therefore refuses the tagged root instead of scanning arbitrary memory. This refusal is correct under its current API; neither skipping the failure nor increasing visit limits is safe.

## Owner repair

Retain the full table graph exactly once. The private owner exposes only lookup and publication; after creation only its entries dictionary gains children. On subsequent dirty leases promote that registered dictionary root, which preserves its new keys/values and follows dictionary reallocation through the existing runtime walk. The class, fill queue, requested map, and id scope remain retained and unchanged. Keep dirty/root state uncommitted on failed promotion, and require a paused lease for each real retention.

This is an owner-local repair, not a claim that arbitrary mutable raw objects can be re-promoted after their original lease. The wider raw aggregate registration limitation remains attributable to the compiler/runtime ABI. A global change from rt_alloc to rt_struct_alloc would add lifetime registry cost to every aggregate and is outside this minimal repair.

The native regression exercises 66 publication leases with allocation churn, reads the first and newest exact values after each lease, requires pre-pause promotion to fail before successful paused retry, and keeps the complete-class graph control and omitted-retention negative control. Native RED is retained in `/tmp/simple-phase2-runner-native-attempt13-20261030/worker-surface-lifetime-owner-debug-run2`: build exit 0, artifact SHA 7a8849cea75befaeb68ce35db4811d7924d7628ed1378ad75525be43ea66eb97, runtime exit 4 at the second publication. `run.stderr` reports `[transient-promote] root refused: value=0x0000b3c4bca1efb1 class=0 heap=1`. Runtime peak RSS was 8,852 KiB; source/runtime hashes stayed unchanged. Native GREEN remains pending the execution owner. Active attempt13 source/evidence remains untouched.
