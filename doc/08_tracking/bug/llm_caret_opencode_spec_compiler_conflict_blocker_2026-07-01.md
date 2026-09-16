# LLM Caret OpenCode Spec Compiler Conflict Blocker - 2026-07-01

## Status

Resolved in source and verified locally with `bin/simple test` after restoring
the missing pure-Simple test/runtime sources in this conflicted checkout.

## Reproduction

```bash
bin/simple test test/01_unit/app/llm_caret/opencode_cli_spec.spl --mode=interpreter
```

## Observed Result

The OpenCode CLI spec source covers argument construction, attach-mode
arguments without shell kill shortcuts, JSON response parsing, and invalid PID
kill rejection. Current local execution passes after restoring the missing
pure-Simple test/runtime sources and fixing OpenCode `sessionID` parsing at the
shared response parser.

The earlier compiler dependency path blocker was an unrelated conflict-marker
chain. After resolving the narrow blockers encountered in
`hir_types.spl`, `_FlatAstBridge/convert_nodes.spl`,
`_FlatAstBridge/module_assembly.spl`,
`hir_lowering/_Items/module_lowering.spl`,
`hir_lowering/_Items/declaration_lowering.spl`,
`treesitter/outline_decls.spl`, `treesitter/outline_members.spl`,
`mir_opt/collection_opt_core.spl`, `mir_opt/_Inline/driver.spl`,
`mir_opt/loop_strength.spl`, `mir_opt/string_builder_opt.spl`,
`mir_opt/predicate_promote.spl`, `mir_opt/_AutoVectorize/recipe.spl`, and
`mir_opt/auto_vectorize_analysis.spl`, `mir_opt/auto_vectorize_validate.spl`,
`mir_opt/_AutoVectorize/rewrite.spl`, and
`mir_opt/pattern/pattern_rule_pass.spl`,
`50.mir/_MirLoweringExpr/expr_dispatch.spl`,
`50.mir/_MirLoweringExpr/method_calls_literals.spl`, and
`50.mir/mir_lowering_stmts.spl`, `50.mir/mir_lowering_ml.spl`,
`50.mir/_MirLowering/module_lowering.spl`, and
`50.mir/_MirLowering/function_lowering.spl`,
`50.mir/host_gpu_lane_queue.spl`, `70.backend/backend/env.spl`, and
`70.backend/backend/interpreter.spl`, `70.backend/backend/llvm_target.spl`,
`70.backend/backend/llvm_lib_translate.spl`,
`70.backend/backend/llvm_lib_translate_expr.spl`,
`30.types/type_infer/traits.spl`, `60.mir_opt/optimizer_manifest.spl`,
`80.driver/driver_build/incremental.spl`, and
`80.driver/driver_pipeline.spl`, the measured passing state was:

```text
bin/simple test test/01_unit/app/llm_caret/opencode_cli_spec.spl --mode=interpreter
PASS test/01_unit/app/llm_caret/opencode_cli_spec.spl
4 examples, 0 failures

bin/simple test test/unit/app/llm_caret/opencode_cli_spec.spl --mode=interpreter
PASS test/unit/app/llm_caret/opencode_cli_spec.spl
4 examples, 0 failures
```

## Impact

OpenCode source and manual evidence are restored in the active tree. The vLLM
readiness lane is also locally unblocked after restoring the missing
`llm_dashboard` collector, MCP lazy JSON helper, IO runtime variants, and torch
dynamic SFFI sources. SGLang static serve planning now uses the documented
`--dp` data-parallel flag instead of the vLLM-style `--dp-size`.
The generated-manual path is unblocked after restoring `std.cli` source files
needed by `simple spipe-docgen`.
`bin/simple check` is now available for the changed OpenCode source after
restoring the binary-dispatched CLI check entry source. In the clean push
candidate, the vLLM serve-plan source is covered by focused readiness specs;
`bin/simple check src/app/llm_runtime/serve_plan.spl` exits 255 after compiler
warning output without a concrete serve-plan diagnostic.

```text
bin/simple test test/01_unit/app/llm_caret/opencode_cli_spec.spl --mode=interpreter
PASS test/01_unit/app/llm_caret/opencode_cli_spec.spl

bin/simple test test/unit/app/llm_caret/opencode_cli_spec.spl --mode=interpreter
PASS test/unit/app/llm_caret/opencode_cli_spec.spl

bin/simple test test/01_unit/app/llm_runtime/vllm_readiness_spec.spl --mode=interpreter
PASS test/01_unit/app/llm_runtime/vllm_readiness_spec.spl

bin/simple test test/unit/app/llm_runtime/vllm_readiness_spec.spl --mode=interpreter
PASS test/unit/app/llm_runtime/vllm_readiness_spec.spl

bin/simple spipe-docgen test/01_unit/app/llm_caret/opencode_cli_spec.spl
OK opencode_cli_spec

bin/simple spipe-docgen test/01_unit/app/llm_runtime/vllm_readiness_spec.spl
OK vllm_readiness_spec

bin/simple check src/app/llm_caret/opencode_cli.spl
All checks passed (1 file(s))

bin/simple run src/app/check/main.spl src/app/llm_caret/opencode_cli.spl
All checks passed (1 file(s))

bin/simple check src/app/llm_runtime/serve_plan.spl
EXIT_CODE=255 after compiler warning output; no serve-plan diagnostic emitted
```
