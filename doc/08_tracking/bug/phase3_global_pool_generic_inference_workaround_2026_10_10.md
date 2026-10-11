# Global pool generic inference diagnostic workaround

Status: OPEN (P1)

Nine calls in core/types.spl use explicit type arguments for diagnostic continuation. This does not repair inference. Tiny explicit-argument control compiled and linked but runtime SIGSEGV; no runtime qualification. Original reproduction and control: test/fixtures/compiler/phase3_global_pool_typeargs_workaround_probe/. Native18 continuation achieved seven source-module HIR receipts; no object was produced.
