# Migration Plan: Rust to Simple

## Philosophy

**Migrate all written code to Simple, keep only library bindings in Rust.**

- ✅ Keep: Library bindings (LLVM, Cranelift, GPU APIs)
- ✅ Keep: Infrastructure (driver, build tools)
- ⚠️ Migrate: All algorithms and logic, even if performance-critical

## Statistics

- Total modules to migrate: 388
- Total lines to migrate: 131,309
- Library bindings (staying): 114

## Migration Phases

### Phase 1: Core Algorithms

- [ ] `lint/checker` (1,982 lines)
  - From: `rust/compiler/src/lint/checker.rs`
  - To: `src/compiler/lint/checker.spl`

- [ ] `error` (1,789 lines)
  - From: `rust/compiler/src/error.rs`
  - To: `src/compiler/error.spl`

- [ ] `interpreter_call/bdd` (1,421 lines)
  - From: `rust/compiler/src/interpreter_call/bdd.rs`
  - To: `src/compiler/interpreter_call/bdd.spl`

- [ ] `interpreter/node_exec` (1,283 lines)
  - From: `rust/compiler/src/interpreter/node_exec.rs`
  - To: `src/compiler/interpreter/node_exec.spl`

- [ ] `hir/lower/stmt_lowering` (1,231 lines)
  - From: `rust/compiler/src/hir/lower/stmt_lowering.rs`
  - To: `src/compiler/hir/lower/stmt_lowering.spl`

- [ ] `interpreter_eval` (1,156 lines)
  - From: `rust/compiler/src/interpreter_eval.rs`
  - To: `src/compiler/interpreter_eval.spl`

- [ ] `lint/mod` (1,089 lines)
  - From: `rust/compiler/src/lint/mod.rs`
  - To: `src/compiler/lint/mod.spl`

- [ ] `interpreter_call/block_execution` (1,079 lines)
  - From: `rust/compiler/src/interpreter_call/block_execution.rs`
  - To: `src/compiler/interpreter_call/block_execution.spl`

- [ ] `codegen/mir_interpreter` (1,058 lines)
  - From: `rust/compiler/src/codegen/mir_interpreter.rs`
  - To: `src/compiler/codegen/mir_interpreter.spl`

- [ ] `hir/lower/expr/control` (1,035 lines)
  - From: `rust/compiler/src/hir/lower/expr/control.rs`
  - To: `src/compiler/hir/lower/expr/control.spl`

- [ ] `pretty_printer` (1,028 lines)
  - From: `rust/compiler/src/pretty_printer.rs`
  - To: `src/compiler/pretty_printer.spl`

- [ ] `blocks/math/backend/torch_eval` (929 lines)
  - From: `rust/compiler/src/blocks/math/backend/torch_eval.rs`
  - To: `src/compiler/blocks/math/backend/torch_eval.spl`

- [ ] `pipeline/module_loader` (838 lines)
  - From: `rust/compiler/src/pipeline/module_loader.rs`
  - To: `src/compiler/pipeline/module_loader.spl`

- [ ] `monomorphize/cache` (805 lines)
  - From: `rust/compiler/src/monomorphize/cache.rs`
  - To: `src/compiler/monomorphize/cache.spl`

- [ ] `compilability` (791 lines)
  - From: `rust/compiler/src/compilability.rs`
  - To: `src/compiler/compilability.spl`

- [ ] `codegen/lean/expressions` (775 lines)
  - From: `rust/compiler/src/codegen/lean/expressions.rs`
  - To: `src/compiler/codegen/lean/expressions.spl`

- [ ] `semantic_diff` (770 lines)
  - From: `rust/compiler/src/semantic_diff.rs`
  - To: `src/compiler/semantic_diff.spl`

- [ ] `web_compiler` (768 lines)
  - From: `rust/compiler/src/web_compiler.rs`
  - To: `src/compiler/web_compiler.spl`

- [ ] `interpreter_control` (751 lines)
  - From: `rust/compiler/src/interpreter_control.rs`
  - To: `src/compiler/interpreter_control.spl`

- [ ] `value_bridge` (750 lines)
  - From: `rust/compiler/src/value_bridge.rs`
  - To: `src/compiler/value_bridge.spl`

- [ ] `lint/types` (734 lines)
  - From: `rust/compiler/src/lint/types.rs`
  - To: `src/compiler/lint/types.spl`

- [ ] `blocks/math/parser` (733 lines)
  - From: `rust/compiler/src/blocks/math/parser.rs`
  - To: `src/compiler/blocks/math/parser.spl`

- [ ] `mock_helper/fluent` (729 lines)
  - From: `rust/compiler/src/mock_helper/fluent.rs`
  - To: `src/compiler/mock_helper/fluent.spl`

- [ ] `hir/types/layout_config` (729 lines)
  - From: `rust/compiler/src/hir/types/layout_config.rs`
  - To: `src/compiler/hir/types/layout_config.spl`

- [ ] `mir/lower/lowering_core` (711 lines)
  - From: `rust/compiler/src/mir/lower/lowering_core.rs`
  - To: `src/compiler/mir/lower/lowering_core.spl`

- [ ] `interpreter_state` (706 lines)
  - From: `rust/compiler/src/interpreter_state.rs`
  - To: `src/compiler/interpreter_state.spl`

- [ ] `runtime_profile/profiler` (706 lines)
  - From: `rust/compiler/src/runtime_profile/profiler.rs`
  - To: `src/compiler/runtime_profile/profiler.spl`

- [ ] `pipeline/execution` (700 lines)
  - From: `rust/compiler/src/pipeline/execution.rs`
  - To: `src/compiler/pipeline/execution.spl`

- [ ] `effects_cache` (686 lines)
  - From: `rust/compiler/src/effects_cache.rs`
  - To: `src/compiler/effects_cache.spl`

- [ ] `concurrent_providers/std_impl` (682 lines)
  - From: `rust/compiler/src/concurrent_providers/std_impl.rs`
  - To: `src/compiler/concurrent_providers/std_impl.spl`

- [ ] `value` (674 lines)
  - From: `rust/compiler/src/value.rs`
  - To: `src/compiler/value.spl`

- [ ] `arch_rules` (671 lines)
  - From: `rust/compiler/src/arch_rules.rs`
  - To: `src/compiler/arch_rules.spl`

- [ ] `monomorphize/deferred` (670 lines)
  - From: `rust/compiler/src/monomorphize/deferred.rs`
  - To: `src/compiler/monomorphize/deferred.spl`

- [ ] `hir/lifetime` (666 lines)
  - From: `rust/compiler/src/hir/lifetime.rs`
  - To: `src/compiler/hir/lifetime.spl`

- [ ] `monomorphize/engine` (662 lines)
  - From: `rust/compiler/src/monomorphize/engine.rs`
  - To: `src/compiler/monomorphize/engine.spl`

- [ ] `mir/effects` (661 lines)
  - From: `rust/compiler/src/mir/effects.rs`
  - To: `src/compiler/mir/effects.spl`

- [ ] `weaving/mod` (657 lines)
  - From: `rust/compiler/src/weaving/mod.rs`
  - To: `src/compiler/weaving/mod.spl`

- [ ] `linker/layout` (652 lines)
  - From: `rust/compiler/src/linker/layout.rs`
  - To: `src/compiler/linker/layout.spl`

- [ ] `predicate` (649 lines)
  - From: `rust/compiler/src/predicate.rs`
  - To: `src/compiler/predicate.spl`

- [ ] `pattern_analysis` (637 lines)
  - From: `rust/compiler/src/pattern_analysis.rs`
  - To: `src/compiler/pattern_analysis.spl`

- [ ] `pipeline/mod` (636 lines)
  - From: `rust/compiler/src/pipeline/mod.rs`
  - To: `src/compiler/pipeline/mod.spl`

- [ ] `mcp` (630 lines)
  - From: `rust/compiler/src/mcp.rs`
  - To: `src/compiler/mcp.spl`

- [ ] `interpreter_contract` (621 lines)
  - From: `rust/compiler/src/interpreter_contract.rs`
  - To: `src/compiler/interpreter_contract.spl`

- [ ] `codegen/buffer_pool` (614 lines)
  - From: `rust/compiler/src/codegen/buffer_pool.rs`
  - To: `src/compiler/codegen/buffer_pool.spl`

- [ ] `linker/interner` (614 lines)
  - From: `rust/compiler/src/linker/interner.rs`
  - To: `src/compiler/linker/interner.spl`

- [ ] `module_resolver/mod` (608 lines)
  - From: `rust/compiler/src/module_resolver/mod.rs`
  - To: `src/compiler/module_resolver/mod.spl`

- [ ] `compilation_context` (602 lines)
  - From: `rust/compiler/src/compilation_context.rs`
  - To: `src/compiler/compilation_context.spl`

- [ ] `lsp_mcp/tools` (600 lines)
  - From: `rust/compiler/src/lsp_mcp/tools.rs`
  - To: `src/compiler/lsp_mcp/tools.spl`

- [ ] `linker/parallel` (597 lines)
  - From: `rust/compiler/src/linker/parallel.rs`
  - To: `src/compiler/linker/parallel.spl`

- [ ] `hir/memory_model` (594 lines)
  - From: `rust/compiler/src/hir/memory_model.rs`
  - To: `src/compiler/hir/memory_model.spl`

- [ ] `pipeline_parallel` (589 lines)
  - From: `rust/compiler/src/pipeline_parallel.rs`
  - To: `src/compiler/pipeline_parallel.spl`

- [ ] `codegen/lean/memory_safety` (583 lines)
  - From: `rust/compiler/src/codegen/lean/memory_safety.rs`
  - To: `src/compiler/codegen/lean/memory_safety.spl`

- [ ] `codegen/lean/traits` (575 lines)
  - From: `rust/compiler/src/codegen/lean/traits.rs`
  - To: `src/compiler/codegen/lean/traits.spl`

- [ ] `mock_helper/coverage` (571 lines)
  - From: `rust/compiler/src/mock_helper/coverage.rs`
  - To: `src/compiler/mock_helper/coverage.spl`

- [ ] `context_pack` (560 lines)
  - From: `rust/compiler/src/context_pack.rs`
  - To: `src/compiler/context_pack.spl`

- [ ] `parallel` (555 lines)
  - From: `rust/compiler/src/parallel.rs`
  - To: `src/compiler/parallel.spl`

- [ ] `codegen/bytecode/compiler` (552 lines)
  - From: `rust/compiler/src/codegen/bytecode/compiler.rs`
  - To: `src/compiler/codegen/bytecode/compiler.spl`

- [ ] `linker/analysis/analyzer` (552 lines)
  - From: `rust/compiler/src/linker/analysis/analyzer.rs`
  - To: `src/compiler/linker/analysis/analyzer.spl`

- [ ] `blocks/math/eval/mod` (545 lines)
  - From: `rust/compiler/src/blocks/math/eval/mod.rs`
  - To: `src/compiler/blocks/math/eval/mod.spl`

- [ ] `hir/analysis/ghost_checker` (542 lines)
  - From: `rust/compiler/src/hir/analysis/ghost_checker.rs`
  - To: `src/compiler/hir/analysis/ghost_checker.spl`

- [ ] `macro_contracts` (535 lines)
  - From: `rust/compiler/src/macro_contracts.rs`
  - To: `src/compiler/macro_contracts.spl`

- [ ] `incremental_builder` (524 lines)
  - From: `rust/compiler/src/incremental_builder.rs`
  - To: `src/compiler/incremental_builder.spl`

- [ ] `project` (521 lines)
  - From: `rust/compiler/src/project.rs`
  - To: `src/compiler/project.spl`

- [ ] `interpreter_unit` (504 lines)
  - From: `rust/compiler/src/interpreter_unit.rs`
  - To: `src/compiler/interpreter_unit.spl`

- [ ] `codegen/lean/emitter` (504 lines)
  - From: `rust/compiler/src/codegen/lean/emitter.rs`
  - To: `src/compiler/codegen/lean/emitter.spl`

- [ ] `codegen/lean/contracts` (502 lines)
  - From: `rust/compiler/src/codegen/lean/contracts.rs`
  - To: `src/compiler/codegen/lean/contracts.spl`

### Phase 2: Medium Modules

- [ ] `codegen/common_backend` (500 lines)
- [ ] `hir/lower/expr/mod` (497 lines)
- [ ] `monomorphize/note_sdn` (494 lines)
- [ ] `build_log` (491 lines)
- [ ] `interpreter_method/primitives` (490 lines)
- [ ] `macro/substitution` (489 lines)
- [ ] `di` (485 lines)
- [ ] `predicate_parser` (484 lines)
- [ ] `blocks/math/eval/tensor_functions` (484 lines)
- [ ] `linker/smf_writer` (483 lines)
- [ ] `blocks/math/eval/standard_math` (482 lines)
- [ ] `interpreter_module/module_evaluator/evaluation_helpers` (482 lines)
- [ ] `api_surface` (481 lines)
- [ ] `value_impl` (467 lines)
- [ ] `macro_validation` (464 lines)
- [ ] `codegen/instr/collections` (464 lines)
- [ ] `mock_helper/coverage_extended/analyzer` (462 lines)
- [ ] `hydration_manifest` (451 lines)
- [ ] `trait_coherence` (451 lines)
- [ ] `codegen/wasm_bindgen_gen` (451 lines)
- [ ] `layout_recorder` (450 lines)
- [ ] `monomorphize/partition` (449 lines)
- [ ] `blocks/math/lexer` (444 lines)
- [ ] `interpreter_patterns` (443 lines)
- [ ] `blocks/math/mod` (443 lines)
- [ ] `blocks/math/ast` (439 lines)
- [ ] `codegen/dispatch` (438 lines)
- [ ] `codegen/lean/types` (433 lines)
- [ ] `runtime_profile/diagram` (431 lines)
- [ ] `hir/lower/memory_warning` (424 lines)
- [ ] `interpreter_module/module_loader` (421 lines)
- [ ] `codegen/instr/closures_structs` (421 lines)
- [ ] `codegen/lean/verification_checker` (421 lines)
- [ ] `value_async` (419 lines)
- [ ] `value_pointers` (418 lines)
- [ ] `i18n/extractor` (416 lines)
- [ ] `monomorphize/cycle_detector` (413 lines)
- [ ] `monomorphize/parallel` (412 lines)
- [ ] `incremental` (410 lines)
- [ ] `codegen/parallel` (409 lines)
- [ ] `mock` (401 lines)
- [ ] `codegen/lean/mod` (400 lines)
- [ ] `lsp_mcp/types` (399 lines)
- [ ] `smf_writer` (397 lines)
- [ ] `mir/function` (397 lines)
- [ ] `interpreter/expr/units` (394 lines)
- [ ] `mock_helper/api_scanner` (391 lines)
- [ ] `interpreter_call/core/function_exec` (390 lines)
- [ ] `runtime_profile/config` (384 lines)
- [ ] `monomorphize/hot_reload` (383 lines)
- [ ] `codegen/emitter_trait` (382 lines)
- [ ] `linker/lazy_instantiator` (375 lines)
- [ ] `monomorphize/tracker` (375 lines)
- [ ] `semantics/binary_ops` (375 lines)
- [ ] `hir/lower/module_lowering/function` (375 lines)
- [ ] `symbol_analyzer` (374 lines)
- [ ] `interpreter_helpers/patterns` (373 lines)
- [ ] `mir/inst_helpers` (373 lines)
- [ ] `hir/lower/memory_check` (368 lines)
- [ ] `monomorphize/util` (362 lines)
- [ ] `value_mock` (359 lines)
- [ ] `interpreter_helpers_option_result` (355 lines)
- [ ] `macro/expansion` (354 lines)
- [ ] `codegen/lean/verification_diagnostics` (354 lines)
- [ ] `hir/lower/type_resolver` (353 lines)
- [ ] `linker/builder` (347 lines)
- [ ] `codegen/instr/core` (347 lines)
- [ ] `codegen/lean/runner` (347 lines)
- [ ] `hir/capability` (346 lines)
- [ ] `blocks/regex` (344 lines)
- [ ] `hir/lower/lowerer` (343 lines)
- [ ] `effects` (342 lines)
- [ ] `interpreter/expr/literals` (339 lines)
- [ ] `codegen/instr/calls` (338 lines)
- [ ] `codegen/backend_trait` (336 lines)
- [ ] `codegen/instr/async_ops` (336 lines)
- [ ] `hir/types/code_layout` (326 lines)
- [ ] `verification_checker` (320 lines)
- [ ] `hir/lower/parallel` (319 lines)
- [ ] `hir/type_registry` (313 lines)
- [ ] `mir/blocks` (311 lines)
- [ ] `pipeline/core` (311 lines)
- [ ] `hir/lower/expr/tensor` (311 lines)
- [ ] `module_resolver/resolution` (309 lines)
- [ ] `codegen/instr/simd_stubs` (309 lines)
- [ ] `interpreter_helpers/collections` (306 lines)
- [ ] `pipeline/lowering` (305 lines)
- [ ] `module_resolver/manifest` (301 lines)
- [ ] `blocks/sql` (298 lines)
- [ ] `module_cache` (297 lines)
- [ ] `blocks/math/backend/auto_select` (296 lines)
- [ ] `linker/builder_macros` (295 lines)
- [ ] `lsp_mcp/mod` (295 lines)
- [ ] `linker/analysis/graph` (292 lines)
- [ ] `mock_helper/mock_policy` (290 lines)
- [ ] `module_resolver/types` (289 lines)
- [ ] `blocks/math/rendering/unicode_text` (286 lines)
- [ ] `error_explanations` (284 lines)
- [ ] `interpreter_helpers/utilities` (283 lines)
- [ ] `codegen/shared` (280 lines)
- [ ] `monomorphize/rewriter` (280 lines)
- [ ] `interpreter_call/core/class_instantiation` (280 lines)
- [ ] `hir/lower/expr/calls` (277 lines)
- [ ] `monomorphize/analyzer` (276 lines)
- [ ] `i18n/locale` (269 lines)
- [ ] `hir/lower/type_registration` (269 lines)
- [ ] `blocks/math/rendering/lean` (267 lines)
- [ ] `blocks/math/backend/mod` (267 lines)
- [ ] `hir/lower/expr/collections` (265 lines)
- [ ] `semantics/cast_rules` (264 lines)
- [ ] `hir/lower/import_loader` (263 lines)
- [ ] `type_inference_config` (261 lines)
- [ ] `codegen/instr/methods` (261 lines)
- [ ] `hir/types/module` (258 lines)
- [ ] `mir/parallel` (257 lines)
- [ ] `hir/lower/expr/access` (254 lines)
- [ ] `macro/invocation` (252 lines)
- [ ] `spec_coverage` (251 lines)
- [ ] `smf_builder` (250 lines)
- [ ] `mir/lower_contract` (248 lines)
- [ ] `codegen/lean/functions` (248 lines)
- [ ] `linker/object_parser` (247 lines)
- [ ] `weaving/matcher` (243 lines)
- [ ] `macro/state` (242 lines)
- [ ] `hir/lower/module_lowering/contract` (242 lines)
- [ ] `text_diff` (241 lines)
- [ ] `blocks/math/rendering/mathml` (241 lines)
- [ ] `hir/types/verification` (241 lines)
- [ ] `method_registry/registry` (239 lines)
- [ ] `hir/lower/module_lowering/validation` (235 lines)
- [ ] `mir/ghost_erasure` (234 lines)
- [ ] `mir/async_sm` (233 lines)
- [ ] `build_mode` (232 lines)
- [ ] `weaving/types` (231 lines)
- [ ] `blocks/math/eval/tensor_broadcasting` (231 lines)
- [ ] `codegen/instr_gpu` (230 lines)
- [ ] `i18n/registry` (226 lines)
- [ ] `hir/types/mod` (221 lines)
- [ ] `blocks/shell` (220 lines)
- [ ] `hir/lower/expr/literals` (219 lines)
- [ ] `mir/generator` (217 lines)
- [ ] `interpreter_call/mock` (214 lines)
- [ ] `codegen/instr/units` (213 lines)
- [ ] `mir/state_machine_utils` (210 lines)
- [ ] `mock_helper/coverage_extended/types` (210 lines)
- [ ] `semantics/type_coercion` (209 lines)
- [ ] `type_check/mod` (208 lines)
- [ ] `interpreter_module/path_resolution` (205 lines)
- [ ] `interpreter/expr/control` (202 lines)
- [ ] `concurrent_providers/mod` (200 lines)

### Phase 3: Small Modules

149 modules, 13,345 lines

