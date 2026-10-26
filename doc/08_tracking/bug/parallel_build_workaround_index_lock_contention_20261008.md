# Parallel native builds contend on workaround-index refresh

Status: observed, root-cause investigation incomplete. No workaround or production change applied.

Observed on Windows dual Xeon, pure producer b467f521, source6bf3276, Phase3 independent 40-process lane. A snapshot of 214 new terminal records contains 66 diagnostic excerpts reporting `workaround writer lock unavailable`; 14 are `OBJECT_EMITTED_UNQUALIFIED` records. Counts are a dated partial snapshot, not the full build failure total.

Evidence packet: `build/rc1-phase3-jobzero-resume40/terminal-ledger.jsonl`. Example module-0624 (`native_all_support.spl`) exits0, emits a structurally checked AMD64 COFF object, and retains this warning. Therefore the warning alone is not evidence of compiler or linker failure.

Current source route: `src/app/cli/native_build_main.spl` calls `refresh_workarounds(false, [])` for each top-level coordinator; only its own native/shard children skip publication. Independent coordinators are not coalesced. `src/app/bug/workaround_store.spl:refresh_workarounds_at` obtains the shared `.simple/workarounds.sdn.lock` with a five-second allowance. The locked refresh loads/encodes the previous index, re-reads linked sources, may loads the bug database, validates the new payload and checks HEAD before atomic publication. The caller reports a warning and proceeds on failure.

Inference: simultaneous coordinators can duplicate discovery and serialize refresh work even when compilation itself is independent. This is distinct from SCV `compile-events/refresh.lock`; reducing SCV decoding does not establish this issue is fixed. No measured attribution of total compile latency to this lock exists yet.

Exact-version follow-up: both frozen6bf and prospectiveb240 already place discovery inside `workaround_refresh_discover_locked`. The dirty/shared checkout inspected initially differs in that ordering; do not use it as the live producer's preimage. Losing coordinators on the frozen version do not perform a full Git status scan before taking this lock. The retained index is153bytes with zero links, so quadratic link-membership work does not explain this observation. Final `git rev-parse` still occurs under the lock even for an unchanged payload; its hold-time contribution is not yet measured.

Required repair investigation: one batch-owned index refresh with exact source/revision/dirty-change binding and explicit refresh receipt, while preserving standalone compiler behavior. Do not skip discovery solely on HEAD (dirty sources can change), reuse stale index coverage, delete locks, or set the native-worker flag on coordinators to bypass unrelated setup. Preserve marker removal, bug-link validation, atomic publication and recovery semantics.

Regression requirements: simultaneous unchanged builds; dirty marker addition/removal with stable HEAD; active indexed source changes; corrupt index; unknown bug ID; writer crash; publication failure; independent checkouts; batch owner exit. Compare refresh count, lock wait/hold, elapsed time and peak memory without changing compiled output. All new regression requirements are UNRUN.
