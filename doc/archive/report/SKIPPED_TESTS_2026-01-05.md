# Skipped Tests Report - 2026-01-05

Complete inventory of skipped/ignored tests across Rust and Simple (.spl) codebases.

## Summary

- **Rust Tests**: 28 tests marked with `#[ignore]`
- **Simple Tests**: 122+ test files marked as SKIPPED
- **Primary Reasons**: Vulkan dependencies, unimplemented modules, BDD framework bugs, macro system issues

---

## Rust Tests (`#[ignore]`)

### 1. Vulkan Tests (24 tests)
**Reason**: Requires Vulkan drivers, GPU, or display server

#### Window Module (`src/runtime/src/vulkan/window.rs`)
- `test_window_creation` - Requires display server

#### Graphics Pipeline (`src/runtime/src/vulkan/graphics_pipeline.rs`)
- `test_graphics_pipeline_builder` - Requires Vulkan drivers
- `test_graphics_pipeline_creation` - Requires Vulkan drivers and shaders

#### Descriptor Module (`src/runtime/src/vulkan/descriptor.rs`)
- `test_descriptor_pool_creation`
- `test_descriptor_set_layout_creation`

#### Render Pass (`src/runtime/src/vulkan/render_pass.rs`)
- `test_render_pass_builder`
- `test_render_pass_creation`

#### Core Vulkan (`src/runtime/src/vulkan/mod.rs`)
- `test_device_creation`
- `test_instance_creation`
- `test_queue_selection`

#### Framebuffer (`src/runtime/src/vulkan/framebuffer.rs`)
- `test_framebuffer_creation` - Requires Vulkan drivers and swapchain

#### Sync (`src/runtime/src/vulkan/sync.rs`)
- `test_fence_creation`
- `test_semaphore_creation`

#### GPU Vulkan Values (`src/runtime/src/value/gpu_vulkan.rs`)
- `test_buffer_creation`
- `test_buffer_value_conversion`
- `test_compute_pipeline_creation`
- `test_descriptor_set_creation`
- `test_image_creation`
- `test_pipeline_cache_creation`
- `test_runtime_buffer_to_value`
- `test_shader_module_creation`
- `test_texture_creation`

**Action Needed**: These tests require CI environment with GPU/Vulkan support or should be run manually on dev machines with proper drivers.

### 2. WASM Tests (2 tests)
**File**: `vulkan-backend/src/driver/tests/wasm_tests.rs`
**Reason**: TODO: Implement WASI stdio capture

- 2 tests pending WASI stdio implementation

**Action Needed**: Implement WASI stdio capture mechanism.

### 3. Compiler Tests (1 test)
**File**: `vulkan-backend/src/compiler/tests/class_invariant_test.rs:225`
**Reason**: Will implement in Phase 3

- Class invariant test deferred to Phase 3

**Action Needed**: Implement in contract system Phase 3.

### 4. REPL Tests (1 test)
**File**: `src/driver/tests/repl_backspace_pty_test.rs`
**Reason**: Documents known rustyline issue

- PTY test for backspace behavior
- Known upstream issue, documented intentionally

---

## Simple (.spl) Tests (SKIPPED)

### Category 1: Macro System Issues (8 files)
**Reason**: Macro system has runtime bugs (const reassignment, shadowing issues)

**Files**:
1. `simple/std_lib/test/system/macros/macro_errors_spec.spl`
2. `simple/std_lib/test/system/macros/macro_system_spec.spl`
3. `simple/std_lib/test/system/macros/macro_intro_spec.spl`
4. `simple/std_lib/test/system/macros/macro_advanced_spec.spl`
5. `simple/std_lib/test/system/macros/macro_templates_spec.spl`
6. `simple/std_lib/test/system/macros/macro_consteval_simple_spec.spl`
7. `simple/std_lib/test/system/macros/macro_consteval_spec.spl`
8. `simple/std_lib/test/system/macros/macro_hygiene_spec.spl`
9. `simple/std_lib/test/system/macros/macro_contracts_spec.spl`
10. `simple/std_lib/test/system/macros/macro_basic_spec.spl`
11. `simple/std_lib/test/integration/macros/macro_integration_spec.spl`

**Action Needed**: Fix macro system runtime bugs in compiler.

### Category 2: Game Engine Modules (10 files)
**Reason**: game_engine module not yet implemented

**Files**:
1. `simple/std_lib/test/unit/game_engine/shader_spec.spl`
2. `simple/std_lib/test/unit/game_engine/scene_node_spec.spl`
3. `simple/std_lib/test/unit/game_engine/physics_spec.spl`
4. `simple/std_lib/test/unit/game_engine/material_spec.spl`
5. `simple/std_lib/test/unit/game_engine/input_spec.spl`
6. `simple/std_lib/test/unit/game_engine/audio_spec.spl`
7. `simple/std_lib/test/unit/game_engine/assets_spec.spl`
8. `simple/std_lib/test/unit/game_engine/actor_model_spec.spl`
9. `simple/std_lib/test/unit/game_engine/effects_spec.spl`
10. `simple/std_lib/test/unit/game_engine/component_spec.spl`

**Action Needed**: Implement game engine module or remove specs if not planned.

### Category 3: Physics Engine (7 files)
**Reason**: physics module not yet implemented

**Files**:
1. `simple/std_lib/test/unit/physics/constraints/joints_spec.spl`
2. `simple/std_lib/test/unit/physics/collision/spatial_hash_spec.spl`
3. `simple/std_lib/test/unit/physics/collision/gjk_spec.spl`
4. `simple/std_lib/test/unit/physics/collision/aabb_spec.spl`
5. `simple/std_lib/test/unit/physics/dynamics/rigidbody_spec.spl`
6. `simple/std_lib/test/unit/physics/core/vector_spec.spl`

**Action Needed**: Implement physics module or remove specs.

### Category 4: ML/Torch (10 files)
**Reason**: ml.torch module not yet implemented

**Files**:
1. `simple/std_lib/test/unit/ml/torch/transformer_spec.spl`
2. `simple/std_lib/test/unit/ml/torch/simple_math_spec.spl`
3. `simple/std_lib/test/unit/ml/torch/recurrent_spec.spl`
4. `simple/std_lib/test/unit/ml/torch/linalg_spec.spl`
5. `simple/std_lib/test/unit/ml/torch/fft_spec.spl`
6. `simple/std_lib/test/unit/ml/torch/dataset_spec.spl`
7. `simple/std_lib/test/unit/ml/torch/custom_autograd_spec.spl`
8. `simple/std_lib/test/unit/ml/torch/autograd_spec.spl`
9. `simple/std_lib/test/unit/ml/torch/tensor_spec.spl`
10. `simple/std_lib/test/unit/ml/torch/nn/activation_spec.spl`
11. `simple/std_lib/test/integration/ml/simple_math_integration_spec.spl`

**Action Needed**: Implement ML/Torch bindings or remove specs.

### Category 5: Parser/TreeSitter (13 files)
**Reason**: parser.treesitter module not yet fully implemented

**Files**:
1. `simple/std_lib/test/unit/parser/treesitter_query_spec.spl`
2. `simple/std_lib/test/unit/parser/treesitter_highlights_spec.spl`
3. `simple/std_lib/test/unit/parser/treesitter_lexer_spec.spl`
4. `simple/std_lib/test/unit/parser/treesitter_incremental_spec.spl`
5. `simple/std_lib/test/unit/parser/treesitter_error_recovery_spec.spl`
6. `simple/std_lib/test/unit/parser/treesitter_parser_spec.spl`
7. `simple/std_lib/test/unit/parser/treesitter/optimize_spec.spl`
8. `simple/std_lib/test/unit/parser/treesitter/language_detect_spec.spl`
9. `simple/std_lib/test/unit/parser/treesitter/grammar_test_spec.spl`
10. `simple/std_lib/test/unit/parser/treesitter/grammar_simple_spec.spl`
11. `simple/std_lib/test/unit/parser/treesitter/grammar_rust_spec.spl`
12. `simple/std_lib/test/unit/parser/treesitter/grammar_python_spec.spl`
13. `simple/std_lib/test/unit/parser/treesitter/grammar_compile_spec.spl`
14. `simple/std_lib/test/unit/parser/treesitter/cli_spec.spl`

**Action Needed**: Complete TreeSitter integration.

### Category 6: LSP/DAP/MCP (11 files)
**Reason**: Language server, debug adapter, and MCP modules not yet implemented

**LSP (7 files)**:
1. `simple/std_lib/test/unit/lsp/semantic_tokens_integration_spec.spl`
2. `simple/std_lib/test/unit/lsp/semantic_tokens_spec.spl`
3. `simple/std_lib/test/unit/lsp/diagnostics_spec.spl`
4. `simple/std_lib/test/unit/lsp/completion_spec.spl`
5. `simple/std_lib/test/unit/lsp/definition_spec.spl`
6. `simple/std_lib/test/unit/lsp/references_spec.spl`
7. `simple/std_lib/test/unit/lsp/hover_spec.spl`

**DAP (3 files)**:
1. `simple/std_lib/test/unit/dap/server_spec.spl`
2. `simple/std_lib/test/unit/dap/protocol_spec.spl`
3. `simple/std_lib/test/unit/dap/breakpoints_spec.spl`

**MCP (1 file)**:
1. `simple/std_lib/test/unit/mcp/mcp_spec.spl`

**Action Needed**: These are being actively developed - check `simple/app/lsp/`, `simple/app/dap/`.

### Category 7: Testing Frameworks (7 files)
**Reason**: Advanced testing features not yet implemented

**Files**:
1. `simple/std_lib/test/system/snapshot/comparison_spec.spl`
2. `simple/std_lib/test/system/snapshot/runner_spec.spl`
3. `simple/std_lib/test/system/snapshot/formats_spec.spl`
4. `simple/std_lib/test/system/snapshot/basic_spec.spl`
5. `simple/std_lib/test/system/property/generators_spec.spl`
6. `simple/std_lib/test/system/property/shrinking_spec.spl`
7. `simple/std_lib/test/system/property/runner_spec.spl`

**Action Needed**: Implement snapshot and property-based testing frameworks.

### Category 8: SDN (Simple Data Notation) (7 files)
**Reason**: SDN modules not yet fully implemented

**Files**:
1. `simple/std_lib/test/unit/sdn/value_spec.spl`
2. `simple/std_lib/test/unit/sdn/roundtrip_spec.spl`
3. `simple/std_lib/test/unit/sdn/compatibility_spec.spl`
4. `simple/std_lib/test/unit/sdn/parser_spec.spl`
5. `simple/std_lib/test/unit/sdn/lexer_spec.spl` - Also has BDD framework scoping bug
6. `simple/std_lib/test/system/sdn/workflow_spec.spl`
7. `simple/std_lib/test/system/sdn/cli_spec.spl`
8. `simple/std_lib/test/system/sdn/file_io_spec.spl`

**Action Needed**: Complete SDN implementation.

### Category 9: Core Module Features (10 files)
**Reason**: Various core modules not yet implemented

**Files**:
1. `simple/std_lib/test/unit/compiler_core/decorators_spec.spl`
2. `simple/std_lib/test/unit/compiler_core/sync_spec.spl`
3. `simple/std_lib/test/unit/compiler_core/random_spec.spl`
4. `simple/std_lib/test/unit/compiler_core/regex_spec.spl`
5. `simple/std_lib/test/unit/compiler_core/context_spec.spl` - Multiple issues
6. `simple/std_lib/test/unit/compiler_core/math_spec.spl`
7. `simple/std_lib/test/unit/compiler_core/dsl_spec.spl`
8. `simple/std_lib/test/unit/compiler_core/pattern_analysis_spec.spl` - BDD framework scoping bug
9. `simple/std_lib/test/unit/compiler_core/attributes_spec.spl` - BDD framework scoping bug
10. `simple/std_lib/test/unit/compiler_core/fluent_interface_spec.spl` - BDD mutable variable bug

**Action Needed**: Implement missing core modules.

### Category 10: BDD Framework Issues (6 files)
**Reason**: BDD framework bugs affecting test execution

**Files**:
1. `simple/std_lib/test/unit/sdn/lexer_spec.spl` - Scoping bug
2. `simple/std_lib/test/unit/compiler_core/pattern_analysis_spec.spl` - Enum definitions in it blocks
3. `simple/std_lib/test/unit/compiler_core/attributes_spec.spl` - Class/function definitions in it blocks
4. `simple/std_lib/test/unit/compiler_core/fluent_interface_spec.spl` - Mutable variable bug
5. `simple/std_lib/test/unit/spec/given_working_spec.spl` - Given/given_lazy not fully implemented
6. `simple/std_lib/test/unit/spec/mock_spec.spl` - Mock library features not implemented

**Action Needed**: Fix BDD framework scoping and mutation bugs in `simple/std_lib/src/spec/`.

### Category 11: Doctest Framework (4 files)
**Reason**: Requires full doctest framework implementation

**Files**:
1. `simple/std_lib/test/system/doctest/runner/runner_spec.spl`
2. `simple/std_lib/test/system/doctest/matcher/matcher_spec.spl`
3. `simple/std_lib/test/system/doctest/doctest_advanced_spec.spl`
4. `simple/std_lib/test/integration/doctest/discovery_spec.spl`

**Action Needed**: Complete doctest framework (Sprint 2 was marked complete, check status).

### Category 12: Verification (3 files)
**Reason**: Verification modules not yet implemented

**Files**:
1. `simple/std_lib/test/unit/verification/regeneration_spec.spl`
2. `simple/std_lib/test/unit/verification/memory_capabilities_spec.spl`
3. `simple/std_lib/test/unit/verification/lean_codegen_spec.spl`

**Action Needed**: Implement verification support modules.

### Category 13: Feature Documentation (3 files)
**Reason**: Feature doc generation not yet implemented

**Files**:
1. `simple/std_lib/test/e2e/feature_generation_spec.spl`
2. `simple/std_lib/test/system/feature_doc_spec.spl`
3. `simple/std_lib/test/system/gherkin/gherkin_spec.spl`

**Action Needed**: Implement feature documentation generation.

### Category 14: Architecture Testing (1 file)
**Reason**: Architecture testing DSL not yet implemented

**Files**:
1. `simple/std_lib/test/system/spec/arch_spec.spl`

**Action Needed**: Implement architecture testing DSL.

### Category 15: Miscellaneous (4 files)
**Files**:
1. `simple/std_lib/test/unit/cli_spec.spl` - CLI module not implemented
2. `simple/std_lib/test/unit/host/datetime_spec.spl` - datetime module not implemented
3. `simple/std_lib/test/unit/tooling/tooling_spec.spl` - tooling module not implemented
4. `simple/std_lib/test/integration/console/console_basic_spec.spl` - spec.console and sys.pty not implemented
5. `simple/std_lib/test/integration/ui/tui/ratatui_backend_spec.spl` - ui.tui.backend.ratatui not implemented

### Category 16: Vulkan/UI Tests with TODOs (9 todos)
**File**: `simple/std_lib/test/unit/ui/vulkan_phase1_validation.spl`
**Reason**: FFI implementation needed

**TODOs**:
- Line 23: Test actual device creation when FFI implemented
- Line 31: Test swapchain creation when FFI implemented
- Line 39: Test render pass creation when FFI implemented
- Line 46: Test shader loading when FFI implemented
- Line 57: Test shader loading when FFI implemented
- Line 67: Test builder pattern when FFI implemented
- Line 78: Test pipeline creation when FFI implemented
- Line 101: Full integration test when FFI implemented
- Line 141: Implement actual clear screen test

**Action Needed**: Implement Vulkan FFI bindings.

---

## Updates (2026-01-05)

### Compilation Errors Fixed ✅
Fixed 7 compilation errors in `interpreter_macro.rs` where statement structs were missing the `is_suspend` field:
- 3x `IfStmt` initializations
- 2x `ForStmt` initializations
- 2x `WhileStmt` initializations

The `is_suspend` field was added for async-by-default suspension operator support (`if~`, `for~`, `while~`).

**Status**: Compiler now builds successfully.

## Recommendations

### Priority 1: Critical Blockers (UPDATED)
1. **~~Fix BDD Framework Bugs~~** ✅ RESOLVED (2026-01-04)
   - Scoping issues - FIXED
   - Mutable variable handling - FIXED
   - Given/given_lazy implementation - Tests need actual implementations, not just skips
2. **Fix Macro System Runtime Bugs** - Blocking 11 test files
   - Const reassignment issues
   - Intro contract shadowing issues

### Priority 2: Infrastructure
3. **CI Vulkan Support** - 24 ignored Rust tests
   - Setup GPU-enabled CI runners or mark as manual-only
   - Document how to run Vulkan tests locally
4. **Complete Doctest Framework** - 4 test files waiting

### Priority 3: Module Implementation
5. **LSP/DAP Implementation** - 11 test files (actively being developed)
6. **SDN Implementation** - 8 test files
7. **Core Module Features** - 10 test files

### Priority 4: Advanced Features (Can be deferred)
8. **Testing Frameworks** (Snapshot, Property-based) - 7 files
9. **Game Engine** - 10 files
10. **Physics Engine** - 7 files
11. **ML/Torch** - 11 files
12. **TreeSitter** - 13 files

### Priority 5: Low Priority
13. **Verification Tools** - 3 files
14. **Feature Documentation** - 3 files
15. **Architecture Testing DSL** - 1 file

---

## Statistics

- **Total Skipped Tests**: 150+
- **Rust**: 28 (19% Vulkan, 7% WASM, 74% other)
- **Simple**: 122+
  - Unimplemented modules: 70%
  - Framework bugs: 14%
  - TODO/Partial: 16%

## Next Steps

1. Create GitHub issues for:
   - BDD framework scoping bugs
   - Macro system runtime bugs
   - WASI stdio capture implementation

2. Evaluate whether to:
   - Continue with game_engine/physics/ML specs (defer to future)
   - Remove specs for features not on roadmap
   - Keep as aspirational specs for community contributions

3. Document Vulkan test running process for developers with GPU access

4. Update feature status in `doc/features/feature.md` to reflect skipped tests
