# MCP native score conversion — OPEN

Frozen source 523 reports unresolved `to_int` at `src/app/mcp/main_lazy_ctx_tools.spl:597` during the Phase 2 MCP build. HIR passed 141/141 modules; MIR failed and produced no complete MCP object.

WORKAROUND(mcp-f64-to-int-20261012) uses explicit `as i64` for the existing scaled score conversion. It preserves truncation toward zero for finite representable values. Native compilation and execution passed four assertions covering zero, positive, negative and sub-milli values. Compile exit 0, object 2952 bytes, strict link exit 0, run exit 0.

Evidence: `/mnt/c/Temp/simple-mcp-score-cast-probe-20261012/receipt.json` and `link-run-receipt.json`; compiler is the manually relinked Phase 3 candidate with the empty-scope runtime repair. This is focused evidence, not full MCP or non-finite/out-of-range numeric qualification.

The underlying native method-lowering defect remains open. Integration, full MCP build and protocol sanity are pending. Regression source: `test/fixtures/compiler/mcp_f64_score_cast/main.spl`.


## 2026-10-25 underlying method repair candidate

Exact release base: `2bb15a0262a0dc13a4b320fe9399072f17973229`. The earlier native primitive alias repair resolves `to_int`/`to_i64`, but its float arm emitted an unguarded signed conversion. LLVM `fptosi` has no defined result for NaN or an unrepresentable input, unlike the reference interpreter's saturating conversion.

The reviewed candidate requires concrete F32/F64 MIR storage, widens F32 exactly, then uses an ordered self-equality NaN guard and exact positive/negative 2^63 thresholds. NaN produces zero, positive overflow/infinity produces i64MAX, and negative overflow/infinity produces i64MIN. Only the bounded interior reaches the truncating cast. Integer and custom method owners retain their prior paths. Storage rejection uses the established fatal-plus-runtime-panic owner; no runtime primitive, provider, P2 or Rust rebuild is introduced.

Validation is not complete. Guarded combined frontend/HIR/MIR/LLVM attempts 02 and 03 each executed four cases with zero passes and four failures, zero skips. Stage markers in 03 locate all failures inside LLVM translation after parsing, HIR, MIR and graph construction, including unchanged integer/custom controls. The common error is `semantic: type mismatch: cannot convert object to int`; a specific SFFI cause is not proven. Peak RSS was 2374912 KiB in 03; source hashes unchanged and quiescent=1. The original integration spec and raw failing receipts remain preserved.

A separate MIR-only graph suite is prepared to validate the source lowering independently; it does not import/call the blocked backend. Guarded run 04 executed all four MIR-only cases: four passed, zero failures/skips/dropped; raw exit 0, peak RSS 1308944 KiB, source hashes unchanged, quiescent=1. The CFG checks verify all four initializing paths assign the actual returned local and only the guarded interior contains the integer cast. This qualifies MIR lowering only; it does not change the original combined LLVM failures. The native fixture has 12 authored boundary cases covering signed zero, fractions, adjacent representable endpoints, infinities, NaN and F32; it has not been executed. Existing production score helpers and source workarounds remain in place. Keep this bug and the grouped MCP source-form bug OPEN until actual compiler-pass and native original-form qualification are complete.
