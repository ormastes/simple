# MCP native score conversion — OPEN

Frozen source 523 reports unresolved `to_int` at `src/app/mcp/main_lazy_ctx_tools.spl:597` during the Phase 2 MCP build. HIR passed 141/141 modules; MIR failed and produced no complete MCP object.

WORKAROUND(mcp-f64-to-int-20261012) uses explicit `as i64` for the existing scaled score conversion. It preserves truncation toward zero for finite representable values. Native compilation and execution passed four assertions covering zero, positive, negative and sub-milli values. Compile exit 0, object 2952 bytes, strict link exit 0, run exit 0.

Evidence: `/mnt/c/Temp/simple-mcp-score-cast-probe-20261012/receipt.json` and `link-run-receipt.json`; compiler is the manually relinked Phase 3 candidate with the empty-scope runtime repair. This is focused evidence, not full MCP or non-finite/out-of-range numeric qualification.

The underlying native method-lowering defect remains open. Integration, full MCP build and protocol sanity are pending. Regression source: `test/fixtures/compiler/mcp_f64_score_cast/main.spl`.
