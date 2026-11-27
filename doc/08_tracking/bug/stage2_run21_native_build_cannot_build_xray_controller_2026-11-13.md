# Run-21 Stage 2 `native-build` cannot build the XRay controller executable (2026-11-13)

Status: open. Blocks the "compiled controller" mode of
`scripts/check/check-xray-native-program-e2e.shs` (`--builder`); the lane runs
the same controller under `simple run` meanwhile.

Binary: `build/bootstrap-fable-21/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`
(pinned source 554460a6b85a, sha256 `4b0796c74d8d…`, bootstrap CLI). Command, from a
clean checkout:

    SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 <stage2> native-build \
      test/fixtures/xray/xray_native_program_host.spl --refresh-source-authority -o /tmp/spy_host

(Without `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` the per-file pool refuses to start
below ~88 GB free; without `--refresh-source-authority` any uncommitted edit is
`SCV-E-ADMISSION: snapshot-index-drift`.)

## Three independent defects, in the order they appear
1. MIR, generic receiver: `for entry in self.storage_entries()` inside
   `AdaptiveMap<K, V>` (`src/lib/nogc_sync_mut/src/collections/adaptive_map.spl`,
   11 sites) fails with `for-in over non-array iterables is not supported by
   native codegen yet (#143)` (`collection mir type: I64`): the generic return
   type `[OrderedMapEntry<K, V>]` is not substituted. Annotating each iterable
   (`val stored: [OrderedMapEntry<K, V>] = self.storage_entries()`) clears all 11
   (verified), which shows the element type is known at the source level.
2. LLVM backend (default): 8 std modules produce invalid IR,
   `'%lN' defined with type 'i64' but expected 'ptr'` — a struct-returning
   static method result is declared `i64` and then used as `ptr`
   (`%l3 = call i64 @lib.common.binary_io.BinaryReader.new(ptr %l0)` followed by
   `ptrtoint ptr %l3`). Modules: `common.binary_io`, `common.encoding.external_text`,
   `common.process.observation_v1`, `common.trace.data.data_observation_aggregator_v1`,
   `nogc_sync_mut.io.process_ops`, `nogc_sync_mut.src.collections.{hashset,adaptive_text_set}`,
   `nogc_sync_mut.trace.xray_native_module_v1`.
3. Cranelift backend: `Failed to compile function: lib.common.sdn.value.SdnValue.as_f64`
   (ICE caught, receipt under `build/ice/`).

A top-level `main()` call is also rejected (`cannot derive module static type
from unresolved initializer`); the controller fixture therefore defines `fn main`
only (the interpreter runs it implicitly).

## Resume
Rebuild Stage 2 from a source with (2) and (3) fixed, then
`sh scripts/check/check-xray-native-program-e2e.shs --simple <seed> --builder <stage2>`.
