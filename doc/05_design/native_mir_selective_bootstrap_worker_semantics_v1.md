# Retained bootstrap worker semantics

Status: independent validation recipe and unit acceptance authored; runtime execution and actual worker integration UNRUN. No bootstrap eligibility change is admitted by this artifact.

The shared architecture is `doc/04_architecture/native_mir_selective_bootstrap_process_v1.md` (B owner). The recipe lives in `src/compiler/80.driver/driver_mir_selective_bootstrap_semantics_v1.spl`. It consumes B's decoded retained context plus receipts produced by A's actual owner reconstruction. Context receipts copied back by a caller are insufficient evidence of reconstruction; the eventual worker must call A's import/readback APIs itself before invoking the recipe.

The expected binding comes from the worker's admitted source fingerprint, existing selective semantic context, physical manifest, actual compiler producer header, selected native backend/target and requested Stage 4 policy. Missing context, identity drift, absent/duplicate/different reconstructed owners and contradictory physical entry ownership fail before bootstrap lowering. The result selects `Closure` or `Entry` and carries explicit `stage4` and `skip_post_chain` values. It never changes environment variables, enables ambient bootstrap, or alters global eligibility.

Serial reference boundaries:

- `driver_pipeline_lowering.spl`'s fixed-entry branch lowers nonentry sources in their source order and the bootstrap entry last. A process finishing early must not replace parent publication order.
- `module_lowering.spl`'s bootstrap branch lowers constants and statics, skips generic templates and extern bodies, resets/adds per-module flat function output and publishes flat module output. This branch must be preserved by a future explicit bootstrap mode rather than substituted with ordinary explicit-native lowering.
- `archive_borrowed_module_v1.spl` currently refuses ambient bootstrap. That guard stays intact until the explicit mode owns every required reconstructed registry and the actual flat entry output has equivalence evidence.
- The post chain is skipped for bootstrap before Stage 4 and runs at Stage 4. The recipe binds this to the requested stage, independently of ambient environment reads.

`driver_mir_selective_bootstrap_entry_last_v1` describes serial adoption order, preserving all nonentry relative ordering and requiring one canonical entry. It is not a replacement for physical manifest admission: existing mono aliases and physical ownership must be validated before adopting this order. D owns the final parent publication integration.

The existing unit runner spec `test/01_unit/compiler/driver/native_mir_selective_bootstrap_semantics_spec.spl` exercises missing/stale identities, registry inventory/equivalence, contradictory entry ownership, both stage policies and entry-last order. These are recipe acceptance tests, not transport or native object equivalence evidence.

Remaining release blockers: A's real snapshots and reconstruction; B's physical-manifest/context binding and bounded file publication; explicit lowerer mode preserving flat output; actual worker and parent wiring; jobs 1 versus 10 object and entry export equivalence; duplicate/missing registry rejection at actual process entry; no source frontend replay; owned failure/cancellation cleanup. Existing SOURCE, resource/HAL, MC/DC/coverage, typed-storage, archive/demand/collection and native-group guards remain mandatory.

Owner: C (`/root/provisional_nested_session_fix`). B owns retained context, A owns registry state, D owns private roots and parent adoption. Merge owner: root. Independent reviewer: Astra. Sidecars: N/A.
