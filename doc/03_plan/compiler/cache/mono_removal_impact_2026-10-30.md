# Monomorphization removal impact and existing async owners

Source: b622509b4daf41d6d8902fed695760975276258d. Read-only scoped inventory; no execution qualification. Latest user direction requests removal of monomorphization and supersedes the earlier REV2 preservation instruction. No semantic deletion is implemented by this report.

## Actual dependencies

- `src/compiler/80.driver/driver_hir_pipeline_passes.spl:288,366` invokes global report and module-scoped specialization paths. Removing only the global invocation leaves module-scoped work.
- `src/compiler/80.driver/driver_mono_publication_v1.spl:40` rejects unspecialized generic calls with E-MONO-033 before MIR. Removing this gate would hide lost symbols.
- `src/compiler/50.mir/_MirLowering/function_lowering.spl:1454` explicitly rejects unsubstituted type parameters with E-MIR-TYPE-TypeParam. Its Any path also fails explicitly; Any is not a qualified generic execution replacement.
- `src/compiler/70.backend/linker/lazy_instantiator.spl:273` constructs the existing TemplateInstantiator. Lazy specialization is another use of the same semantic machinery, not an alternative erased implementation.
- `src/compiler/80.driver/cache/hir_mono_archive_consumer_v1.spl` and `hir_mono_replay_selection_v1.spl` depend on MonomorphizationPass for archive admission/replay. Nominal identity, body availability, selective emission, relocation and deterministic nested demand closure are part of this owner.
- `src/compiler/99.loader/loader/smf_cache.spl` imports monomorphization note metadata. Existing archives/loaders and public exports in `40.mono/__init__.spl` require an explicit compatibility decision.

A scoped search found no qualified alternative generic native execution route. This is an inventory conclusion, not a proof of whole-repository absence. Interpretation or type erasure cannot be assumed to preserve native layout, trait dispatch, addressable generic functions, exported symbols, nominal identity or template-package behavior.

## Removal dependency order for review

1. Resolve the language consequence: retain generics through a replacement execution model, or reject generic native programs explicitly. Removing scheduling only does not fulfill literal semantic removal.
2. Freeze acceptance fixtures for generic functions, nested demand, generic structs/classes and layout, trait/coherence dispatch, address taking, exported specialization, unavailable template bodies and cross-module archives.
3. If retaining generics, implement and qualify the replacement producer and ABI first. If disabling them, diagnose at the language admission boundary before cache publication or MIR, without silently skipping bodies.
4. Migrate both driver invocation paths, archive replay/admission and linker lazy instantiation together. Keep current explicit errors until replacement evidence exists.
5. Version or retire persisted metadata contracts and update imports/exports; then remove unreachable implementation and validate real outputs with the admitted compiler. No broad deletion is authorized by a text match alone.

## Existing asynchronous resources

- `nogc_async_mut/concurrent/lockless_map_i64.spl` and `async_ring/async_ref.spl`: bounded scalar shared outcome, direct atomic core, canonical SimpleRing adapter. No new map is needed. The adapter explicitly requires owner wake draining and quiescent arena destruction; it is not an automatic executor.
- `compiler/80.driver/cache/daemon/cache_single_flight_v1.spl`: existing production owner with callers in generic instance/TLDR views, macro expansion, AOP match, TLDR summary and cache daemon. Its Future.pending() return is detached; stable AsyncRef adoption is not already wired.
- `compiler/80.driver/cache/source_reader_v1.spl`: existing async interface, but default methods wrap completed synchronous reads in Future.from_value; await_now polls with a bound. Interface presence is not nonblocking I/O evidence.
- `lib/common/task_runner/` remains the execution owner; this slice creates no replacement scheduler and does not modify BuildRunner.

## Isolated corrective slice

Invalid live-scope AsyncRef entries previously appeared Pending, or NotStarted/cancellation through other adapters. New explicit InvalidReference outcomes prevent those states from being confused with work awaiting completion. The unsafe live-scope requirement remains: arbitrary or freed addresses cannot safely be validated. Unit and ring integration cases were written before the implementation but remain UNRUN because no qualified Linux CLI is available. No hardware concurrency, TDD RED/GREEN or monomorphization integration claim is made.

The public AsyncRefStateI64 and AsyncRefError enums gain InvalidReference; exhaustive downstream matches must add it. The only other exhaustive source match found in the scoped repository search was updated in accessor_native_diagnostic.spl. Existing valid reference semantics and error payloads (Failed(i64)) are unchanged. Sol reviewed the source diff with no blocking issue; requested exact ring-token assertions were incorporated. Full mono/resources integration is not implemented and is superseded by the removal impact review.
