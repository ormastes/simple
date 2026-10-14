# Cached native capsule reconstruction drops emission authority

Status: FIX CANDIDATE. Static source review proves the mismatch; successor-native cache qualification is pending.

The current native output path emits each uncached module using the resolved effective backend, the selected provider receipt hash, and its complete module witness and witness reason. `FrozenNativeModuleCapsuleV1.expected_identity` includes all four fields. The former cache-hit reconstruction in `driver_aot_native_output.spl` passed the unresolved requested backend and omitted the provider and witness arguments. Defaults supplied an empty provider/witness and `missing-witness-facts`. An object produced with a complete witness therefore failed capsule-receipt verification even when its stored module witness had already matched the current witness.

The repair reconstructs cached capsules using the same resolved backend, provider receipt hash, current complete witness and current reason as emission. Source-snapshot, witness-match, object-path, disk existence, MIR, storage and receipt checks remain mandatory. Stored identities are never rewritten, and no receipt is admitted by weakening its authority. This defect is proven in current source; it does not establish the specific cause of the older pinned Stage 2 producer's misses documented in `pinned_stage2_changed_entry_cache_rebuilds_dependencies_2026-10-13.md`.

The focused behavior spec is `test/01_unit/compiler/driver/native_cache_capsule_authority_spec.spl`. It constructs actual current capsules and checks unchanged authority equality plus missing-facts, changed-provider and changed-witness inequality. The spec is authored but unrun: its `CompileContext` dependency reaches the full compiler closure, and the available immutable Stage 2 producer cannot qualify that closure within the previously failed memory boundary. There is no smaller existing capsule owner to exercise independently without copying production logic. This fixture is a contract guard, not proof of driver cache reuse.

Native acceptance must use a coherent successor containing the repair. Repeat the changed-entry fixture after dependency preparation, require actual imported-object hits and one entry rebuild, run the resulting executable, and retain the producer/source/target/provider identities, per-module witness decisions and object receipts. Changed witness/provider/MIR/source controls must continue to reject reuse. No <=100 ms or Phase 3 completion claim is supported by this patch alone.

Linux AArch64 object/link review found no additional proven publication defect: current module collection authenticates individual capsules, retains successful cache entries before aggregate failure, and refuses the final link after any recorded failure. The historical Windows archiver command-length failure uses a different output/host lane and is not claimed repaired here.

Owner: Codex Phase 3 incremental completion logic lane. No commit or push.
