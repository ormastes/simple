# Item 5 imported-generic HIR probe: MIR worker crash

Status: OPEN (2026-10-11). The focused probe has no executable native result.

The probe at `test/fixtures/compiler/mono_imported_name_hir_probe.spl` compiles the current-source monomorphizer as a library and checks exact owner-qualified call names for two imported generic functions. It uses the admitted pure-Simple Stage 2 bootstrap compiler, LLVM/core-C, entry closure, one binary, and `SIMPLE_NO_STUB_FALLBACK=1`.

Three bounded verify/fix cycles:

1. `build/mini_builds/item5_mono_name_hir_20261011/build.log`: one HIR failure. The copied unit harness imported stale `Module`; the current parser owner exports `ParserModule`. The unit spec and native probe now use `ParserModule`.
2. `build/mini_builds/item5_mono_name_hir_retry_20261011/build.log`: HIR completed 300/300; monomorphization refused seven calls to `_sffi_transient_heap_promote` on indexed inner module owners because it could not infer `T`. The seven calls now state their existing element types explicitly. This changes no ownership or promotion order.
3. `build/mini_builds/item5_mono_name_hir_typed_20261011/build.log`: HIR completed 300/300, monomorphization reported `generic_fns=9 call_sites=60 specializations=38 unresolved=0`, then the native-build worker terminated with signal 11 in MIR lowering before producing a binary. No current crash report appeared under `/var/crash`.

The third-cycle limit stops another probe build in this session. The successful monomorphization is source-level evidence only. It does not prove the native imported-generic link fix, the exact call-name assertions at runtime, the dynlib gate, or Item 5 size/startup/RSS gates. Next diagnostic needs a MIR worker backtrace and a smaller HIR-only route or a repaired compiler worker, followed by the original four-module dynlib gate.
