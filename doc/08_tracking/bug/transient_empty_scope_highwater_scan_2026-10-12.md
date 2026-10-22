# Empty transient scopes repeatedly scan historical raw allocation capacity

STATUS: focused owner1 native SOSIX validation PASS; full compiler/application qualification remains with parent.

The actual MCP worker was sampled in `rt_core_reclaim_transient_raw` during inventory validation. Another GDB sample recorded capacity 2,097,152 and live count zero. The runtime previously scanned every slot and cleared the entire table on each empty cleanup; memory-owner mode invokes cleanup twice per scope end. This makes later empty scopes pay the historical peak table size.

The seven-line fix returns early for zero live entries. If erased entries remain, it first clears tombstones. Nonempty owned/borrowed/guarded freeing and all outer scope state, thread ownership and memory-provider callbacks remain unchanged. The invariant is that insertion increments the live count, erase replaces a live entry with a tombstone and decrements it, and clear removes both. Empty plus zero tombstones therefore contains no entry requiring work. No table shrink or allocator ownership rewrite is introduced.

## Exact runtime and measurement

Baseline runtime source is cc6822c6b52c403e65e61c6fd2ec5cbd4c6f0a20, frozen integrated capsule. Only runtime_native.o was rebuilt with its original LLVM23, ABI1, owner1, timestamp/dynload owner, standalone and O2 flags. All 40 archive member names and global defined symbol multiset match; only runtime_native.o bytes differ. Commands, hashes, logs and exact sources are adjacent to receipt.json.

The real Simple probe allocates and reclaims 750,000 eight-byte objects, observes the same 2,097,152-capacity/zero-live/zero-tombstone state, then measures 21 cohorts of ten empty scopes. It asserts nested begin fails and repeated end fails. Baseline p50/p95 per scope: 5,457.6/6,938.3 microseconds. Candidate: 0.0/0.1 microseconds, at the timer-resolution floor; no precise speedup ratio or zero-cost claim is made.

Inferior /proc RSS before/after samples is identical: 60,576 -> 60,768 KiB. Peak is 76,036 baseline and 76,228 candidate, a 192 KiB (0.25%) difference under the declared 131,072 KiB limit. Capacity is intentionally retained. These finite measurements provide no long-running leak proof. The ordinary p95 time ratio plus peak memory ratio is approximately 1.003, below 2, although latency resolution limits the time ratio precision.

## Ownership and guard regression

The real-runtime Simple fixture passes with guard sampling disabled and enabled: explicit free/tombstone-only scope, paused borrowed allocation, promotion, preserved payload bytes, registry removal, and subsequent/nested/repeated scope transitions. Peaks are 4,548 and 4,780 KiB. A separately compiled C runtime-boundary fixture requires SIGSEGV from exactly four forked child reads after explicit free or owned scope reclaim. Its parent verifies promoted and paused payloads survive scope end and exits zero; peak 2,828 KiB. Core dumps are disabled and the parent run has a ten-second deadline. These expected child faults are the negative contract, not uncontrolled compiler crashes.

## Scope and remaining qualification

The optimization is appropriate for the measured owner1 archive. The no-memory-owner build and Windows/macOS/BSD/SimpleOS have not executed. No full compiler, Phase1 suite or MCP end-to-end latency PASS is claimed. Parent owns cached-object manual relink, real Hello and test-owner qualification before deployment. Main checkout and existing runtime archives remain untouched; user owns cherry-pick/integration. One runtime fix cycle was used. Do not repeat passing focused checks unchanged.

Additional qualification: the changed runtime translation unit also compiles with `SIMPLE_RUNTIME_MEMORY_OWNER=0` using the frozen ABI1 flags (exit 0, object 681,680 bytes). This is a Linux compile-only result; owner0 execution and all non-Linux execution remain unqualified. The manually relinked cached Phase 3 compiler compiled and executed fresh Hello successfully; the full test owner still fails an independently confirmed null callback.
