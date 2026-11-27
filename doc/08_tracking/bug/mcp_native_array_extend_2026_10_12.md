# MCP native array extend — OPEN

Frozen source523, P2producer892b reports unresolved method call extend at src/app/mcp/main_lazy_caret_tools.spl:94 after141/141HIR modules pass. No object is emitted.

Tagged workaround appends each argv item with existing array push, preserving environment assignments followed by compiler path and all tool arguments in order. No tool/capability is removed. Regression covers prefix/order and empty append; six assertions passed in the focused Phase 3 native fixture (compile exit 0, object 6824 bytes, strict link exit 0, run exit 0). Evidence: `/mnt/c/Temp/simple-mcp-argv-append-probe-20261012`.

Underlying native array extend lowering remains OPEN. The tagged workaround is qualified for this focused append contract. Full MCP qualification and integration remain pending; the compiler lowering defect remains open.

**Revalidated 2026-11-02: still plausible because the report title (Native array extend unresolved in MCP) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 status: fix-implemented-verification-pending
Builtin `Array.extend`/`merge` lowering exists (`lower_unresolved_array_merge`, `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:5385`). MIR-level regression `test/01_unit/compiler/mir/array_extend_lowering_spec.spl` passes on the seed (`bin/simple.exe run`). Repro for closure: native-build `src/app/mcp/main_lazy_caret_tools.spl` with the stage3 binary after removing the tagged push-loop workaround; expect no unresolved `extend`. Workaround tag kept.
