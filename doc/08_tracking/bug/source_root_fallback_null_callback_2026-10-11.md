# Native loader fallback dispatches through null function pointer

Status: source repair candidate; rebuilt native qualification pending.

Producer SHA256
`fcdb2397a1a681c2b6fe32ada16585b4e24afc37f6397a34db55a183dffb73c2`
crashes before HIR when a selected source-root lookup returns `Missing`.
`source_root_resolution_with_fallback_v1` calls the supplied
`_driver_resolve_entry_import` function value, but native dispatch reaches PC 0.
This is distinct from the earlier enum text formatting failure.

Independent backtrace:
`/home/yoon/dev/simple-foreign-field-owner-20261011/build/native_probe/foreign-field/integrated/source-closure-backtrace.log`.
Frame 1 is the fallback helper at `0x4cc048`; frame 2 is
`driver_source_pipeline_loading.CompilerDriver_load_sources_impl`.
Two unchanged foreign-owner fixtures exited 139. The CUDA owner fixture also
failed source closure with worker exit -139, zero claimed/sealed modules and
outer exit 1; its log is `build/cuda-policy/source-root-fcdb-build.log`.

The loader does not need a callback abstraction. Its caller now matches
`Found`, `Missing`, and `Ambiguous` directly; only `Missing` calls the canonical
resolver. The removed function-value API's four tests were removed, rather
than claiming they pass. The eight numbered/enum native probe assertions and
filesystem ambiguity/default regressions remain. No compiler function-value
codegen fix is claimed; the general dispatch defect remains open.

The removed cross-module callback shape is preserved as a dedicated source
fixture in `test/fixtures/compiler/source_root_named_callback_probe/main.spl`,
with separate callback owner and named target modules. It expects
`NAMED_CALLBACK_PASS` and exit 0. This fixture has not run: the current producer
crashes in its own loader before it can compile such a fixture. The observed
reproducer is the producer's loader and retained backtrace, not a claimed
failure of this newly extracted standalone fixture.

Required qualification: rebuild the producer, run the owner probe and normal
missing-root closure, execute both ambiguous-overlay/default regressions, and
prove disabled CUDA source closure and linked-symbol exclusion. No private
compiler build or second attempt with the crashing producer was performed.
