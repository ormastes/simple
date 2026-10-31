# typeparam MIR failure: static generic class factory leaves T unsubstituted (2026-10-31)

## Root bug
`Future.from_value(x)` / `Future.pending()` (static fns of generic `class Future<T>`,
src/lib/nogc_async_mut/async/future.spl) reach MIR lowering with `T` unsubstituted in the
stage2 compiler: `E-MIR-TYPE-TypeParam` (src/compiler/50.mir/_MirLowering/function_lowering.spl).
Explicit `Future<bool>.from_value(..)` and a typed `val f: Future<bool> = ...` do not help
(verified with pinned stage2). Direct construction
`Future(state: [], poll_result: Poll.Ready(v))` under a concrete return type lowers fine.

## Workaround sites (all tagged `@workaround bug=typeparam-mir-20261031`)
- src/compiler/80.driver/cache/module_artifacts_v1.spl: helper `_ready_future_bool_v1`; 7 call sites in `module_artifact_publish_atomic_async_v1`
- src/compiler/80.driver/cache/source_reader_v1.spl: helpers `_ready_future_text_v1`, `_ready_future_module_v1`; 2 sites in `SourceReader`
- src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl: helpers `_ready_future_blob_v1`, `_pending_future_blob_v1`; 2 sites in `future`

## Removal condition
Remove once the root fix (mono/HIR substitution of class type args for static generic
calls) is in the stage2 used for bootstrapping.
