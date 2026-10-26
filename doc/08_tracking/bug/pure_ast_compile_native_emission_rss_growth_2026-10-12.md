# Pure AST compile exceeds5GiB during native emission

Status: reproduced; root-cause fix OPEN. Bug DB reconciliation pending.

Producer: admitted retained Phase2 Pure executable SHA a6b18fd84c5f88a48afa0beaf61434f39678155fb0f0ed01127db25a28cf5078.
Packet: build/native_probe/pure-loader-api-20261011-astra/hir-minimal-import-criterion.
Request SHA522972419d65ccb1388c9efe3cc65b3fb61920d1a45868b96929b3ac01c363d0.
Terminal RESULT SHA41ed1eaa75c9d5bb82a828a21a46845bd67bc9ea1ce47f5b35a3320e90ff75aa.

Actual parallel ordinary-mode alias-explicit and physical-explicit real AST accessor fixtures were dispatched with separate frozen source roots/cache/TEMP. Each requests40threads; active40worker execution is not established. No Rust seed or ambient SIMPLE_BOOTSTRAP fallback.

Alias48modules and physical47modules reached borrow checking, async processing, MIR optimization, AOP and native compilation. Last observed native compile progress11/48 alias and10/47 physical; both writable caches contain0 .obj/.o files, so these counters do not prove object publication. Both exceeded sampled5GiB RSS cap: alias5252164KiB/92.069seconds, physical5260352KiB/92.882seconds. Native exits88, reason rss-cap-exceeded; final Job active0; all5742pinned inputs unchanged. No runtime assertion executed. No whole-loader attempt3 consumed.

Do not claim import correctness from progress alone. Inspect actual terminal logs and cache artifacts before object reuse. Requested thread count, completed frontend counters and filesystem object presence are not runtime or lineage admission.

Next focused investigation: attribute growth to LLVM text builders, retained MIR/module graphs, runtime C subprocesses and native emission lifetime, using stage-specific sampled RSS/actual process membership. Compare default/nonbootstrap behavior and independent contexts. Require real regression and similar prevention coverage; preserve native emission semantics, no disabling ownership checks or silently pruning imports/tests. A larger diagnostic cap requires an explicit revised request and independent review, not unchanged automatic replay.

Full Phase3/test binaries/Phase4 and0.1second latency targets remain incomplete. Astra side-agent execution currently fails authentication refresh; prior saved preparation review was used with root exact seal/controller/input and capacity review for this attempt.
## Current-source scheduling inspection

Current shared driver_aot_native_output.spl around2039-2065 explicitly states that the direct ParallelBuilder.build route runs sequentially in-process. An admitted stateful backend session resolves its provider lane to1; a larger configured thread count is not evidence of active parallel codegen. Existing report: doc/08_tracking/bug/native_build_step5_serial_threads_ignored_2026-09-04.md.

Around1988 all uncached modules are frozen into one capsule batch before emission. driver_types.spl:freeze_native_module_capsules_v1 validates storage identities and gathers MIR module payloads; _compile_frozen_module_capsule receives that batch. This suggests concrete profiling boundaries (before/after capsule freezing, per-module LLVM translation, native provider return and result collection), but does not prove copying or a leak. Current source is not automatically identical to retained producer bytes; compare authenticated producer owners before attributing historical memory growth.

Keep separate issues: actual low codegen concurrency on the documented direct route versus measured per-process memory growth. Raising jobs or memory caps cannot qualify a fix to either. A safe parallel route needs independent owned backend sessions/output buffers and parent-authoritative publication, not concurrent access to the existing stateful session.
## Producer/current ownership comparison

Decoded exact file-hex rows from the authenticated producer source-inputs-before.txt:

- driver_aot_native_output.spl: producer8bf8394bbd7e3bd04ed4a3727df22d0e98a3cd00aae52f9b65aeefb525e9c560; current7dde99367b3994db64b19620aa4959b666eee7558706e4403dba15ae251ac2fc.
- driver_types.spl: producerefd3c20d13912f90e79c9a022dc5864d7e4187368a351f80de1c95d824ea55fe; currentcd4479c22e8535cf34448fdebd82ceb483887be5424d04b64db4b1219b70f3cd.

Both differ. Current capsule freezing and serial-provider source observations therefore cannot identify the retained producer's historical allocation mechanism. Obtain matching historical bytes or actual allocation traces before designing a production repair.