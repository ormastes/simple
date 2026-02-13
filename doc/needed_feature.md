# Needed Features - Simple Language

**Last Updated:** 2026-02-14
**Test Audit Complete:** 73+ tests verified

This document tracks pending features, skipped tests, TODOs, and stub implementations that need to be completed.

**IMPORTANT:** Recent test audit discovered that **30+ tests marked @skip/@pending actually PASS!** See the "WORKING BUT UNDOCUMENTED" section below and [FEATURES_THAT_WORK.md](FEATURES_THAT_WORK.md) for details on fully functional features.

## 1. Language Features (Parser/Syntax)

### Keywords Not Supported
- `async`/`await` - Async syntax not fully implemented
  - `test/feature/async_features_spec.spl` - @skip
  - `test/feature/stackless_coroutines_spec.spl` - @skip
  - `test/unit/std/async_spec.spl` - @skip
  - `test/unit/std/async_host_spec.spl` - @skip
  - `test/unit/std/async_embedded_spec.spl` - @skip
  - `test/unit/app/interpreter/ast_convert_expr_spec.spl` - @skip

- `spawn` - Thread/process spawning not implemented
  - `test/feature/actor_model_spec.spl` - @skip
  - `test/unit/lib/qemu_spec.spl` - @skip
  - `test/unit/std/console_basic_spec.spl` - @skip
  - `test/unit/std/arc_spec.spl` - @skip

- `repr` - Memory representation attributes
  - `test/unit/compiler/baremetal_syntax_spec.spl` - @skip

- `macro` - Macro system not supported
  - `test/system/macro_consteval_simple_spec.spl` - @skip

### Syntax Features
- **Set literals** `s{...}` - Requires runtime rebuild with new parser
  - `test/feature/set_literal_spec.spl` - @skip
  - `test/feature/custom_literal_spec.spl` - @skip

- **Bitfield syntax** - Not implemented yet
  - `test/feature/bitfield_spec.spl` - @skip

- **Union types** - Implementation pending
  - Union type implementation (#37)

- **Parser error recovery** - Module std.parser not available in runtime
  - `test/feature/parser_error_recovery_spec.spl` - @skip

### Parser Bugs/Limitations
- Match case with inline arrays causes parser bug
  - `test/unit/compiler/match_empty_array_bug_spec.spl` - @skip

- `print()` returns nil in runtime, not the printed value
  - `test/system/print_return_spec.spl` - @skip

- Runtime value syntax issues (nil identifier)
  - `test/unit/std/runtime_value_spec.spl` - @skip

## 2. Compiler Features

### Type System
- Effect inference and annotations
  - `test/feature/effect_annotations_spec.spl` - @pending
  - `test/unit/compiler/effect_inference_spec.spl` - @skip

- Advanced generics
  - `test/feature/generics_advanced_spec.spl` - @pending

- Default trait methods
  - Not implemented (noted in parser_declarations_spec)

### Backend/Codegen
- **Generator state machine codegen**
  - `test/feature/generator_state_machine_codegen_spec.spl` - @pending

- **Native FFI** - Some functions stub/not implemented
  - `test/unit/compiler/backend/native_ffi_spec.spl` - Unsafe groups @skip (rt_execute_native hangs)
  - Various FFI wrappers needed (see TODOs section)

- **Linker integration**
  - `test/unit/compiler/linker_spec.spl` - @pending/@skip
  - `test/unit/compiler/linker_context_spec.spl` - @pending/@skip
  - `test/unit/compiler/note_sdn_spec.spl` - @pending/@skip

- **JIT context**
  - `test/unit/compiler/jit_context_spec.spl` - @pending/@skip

- **Backend capabilities**
  - `test/unit/compiler/backend/backend_capability_spec.spl` - @skip
  - `test/unit/compiler/backend/instruction_coverage_spec.spl` - @skip
  - `test/unit/compiler/backend/exhaustiveness_validator_spec.spl` - @skip
  - `test/unit/compiler/backend/differential_testing_spec.spl` - @skip

### Verification
- **Lean 4 integration** - Not implemented (returns empty results)
  - `test/unit/compiler/verification/lean_basic_spec.spl` - @pending/@skip
  - `test/unit/compiler/verification/verification_diagnostics_spec.spl` - @pending/@skip
  - src/app/lsp/handlers/verification.spl:37 - WARNING: not implemented

### TreeSitter/Parser Integration
- Position tracking not implemented yet
  - start_byte(), end_byte(), start_point(), end_point() return dummy values

- Parent/sibling navigation not implemented
  - parent(), next_sibling(), prev_sibling() return None

- Error tracking not implemented
  - is_error() returns false

- Incremental parsing - needs edit information tracking
  - Currently reparse entire source

- Tests pending:
  - `test/unit/compiler/parser/lexer_contextual_keywords_spec.spl` - @pending
  - `test/unit/compiler/parser/treesitter_incremental_spec.spl` - @pending
  - `test/unit/compiler/parser/treesitter_error_recovery_spec.spl` - @pending
  - `test/unit/compiler/parser/treesitter_tree_real_spec.spl` - @pending/@skip
  - `test/unit/compiler/parser/treesitter_parser_real_spec.spl` - @pending/@skip
  - `test/unit/compiler/parser/treesitter_highlights_spec.spl` - @pending
  - `test/unit/compiler/parser/grammar_compile_spec.spl` - @pending

## 3. Runtime/Standard Library

### Async/Concurrency
- Async/await syntax not fully implemented (see section 1)
- Actor model/system not implemented
  - `test/feature/actors_spec.spl` - @skip
  - `test/feature/actor_model_spec.spl` - @pending/@skip
- Thread support (spawn keyword)
- Stackless coroutines
  - `test/feature/stackless_coroutines_spec.spl` - @skip

### File I/O
- Extended file I/O operations
  - `test/feature/file_io_extended_spec.spl` - @pending/@skip
  - `test/system/file_io_spec.spl` - @pending/@skip
  - `test/unit/std/infra/file_io_spec.spl` - @pending/@skip
  - `test/unit/std/file_find_spec.spl` - @pending/@skip

### System Integration
- Environment variables
  - `test/unit/std/env_spec.spl` - @pending/@skip

- Process management
  - `test/unit/std/process_spec.spl` - @pending/@skip

- System FFI
  - `test/unit/std/sys_ffi_spec.spl` - @pending/@skip

- Resource limits
  - `test/unit/std/resource_limits_spec.spl` - @pending/@skip

### DateTime
- DateTime functionality
  - `test/unit/std/datetime_spec.spl` - @pending/@skip
  - `test/unit/std/datetime_ffi_spec.spl` - @pending/@skip

### Testing Framework
- Lexer FFI tests
  - `test/lib/std/compiler/lexer_ffi_test.spl` - @pending

- Mock verification
  - `test/unit/std/mock_verification_spec.spl` - @pending

- Contract testing
  - `test/unit/std/contract_spec.spl` - @pending

- Fuzzing support
  - `test/unit/std/fuzz_spec.spl` - @pending/@skip

### Other Standard Library
- Logging
  - `test/unit/std/log_spec.spl` - @pending/@skip

- Dependency injection
  - `test/unit/std/di_spec.spl` - @pending/@skip

- Database integration
  - `test/unit/std/db_spec.spl` - @pending/@skip

- Configuration
  - `test/unit/std/config_spec.spl` - @pending/@skip
  - `test/unit/std/infra/config_env_spec.spl` - @pending

- CLI minimal
  - `test/unit/std/cli_minimal_spec.spl` - @pending

- SDN minimal
  - `test/unit/std/sdn_minimal_spec.spl` - @pending

- JSON improvements
  - `test/unit/std/improvements/json_spec.spl` - @pending

- Mock phases
  - `test/unit/std/mock_phase5_spec.spl` - @pending
  - `test/unit/std/mock_phase6_spec.spl` - @skip
  - `test/unit/std/mock_phase7_spec.spl` - @skip

- Misc std tests
  - `test/unit/std/helpers_spec.spl` - @skip
  - `test/unit/std/list_compact_spec.spl` - @skip
  - `test/unit/std/lexer_spec.spl` - @pending
  - `test/unit/std/context_spec.spl` - @skip

## 4. Application Features

### LSP (Language Server Protocol)
All LSP features are pending/skipped:
- `test/unit/app/lsp/references_spec.spl` - @pending/@skip
- `test/unit/app/lsp/hover_spec.spl` - @pending
- `test/unit/app/lsp/definition_spec.spl` - @pending
- `test/unit/app/lsp/document_sync_spec.spl` - @pending/@skip
- `test/unit/app/lsp/message_dispatcher_spec.spl` - @pending/@skip
- `test/unit/app/lsp/server_lifecycle_spec.spl` - @pending/@skip
- `test/unit/app/lsp/diagnostics_spec.spl` - @pending/@skip
- `test/unit/app/lsp/completion_spec.spl` - @pending/@skip

Features noted as "not implemented":
- textDocument/codeAction handler

### Debugger (DAP)
- Condition evaluation not implemented (returns false)
- Variable evaluation returns error

### MCP Integration
- `test/unit/app/mcp/failure_analysis_spec.spl` - @skip (module not available)
- `test/unit/app/mcp/prompts_spec.spl` - @skip (syntax issues)

### Package Management
- `test/unit/app/package/semver_spec.spl` - @skip
- `test/unit/app/package/package_spec.spl` - @skip
- `test/unit/app/package/manifest_spec.spl` - @skip
- `test/unit/app/package/lockfile_spec.spl` - @skip
- `test/unit/app/package/ffi_spec.spl` - @skip

### Tooling
- Arg parsing
  - `test/unit/app/tooling/arg_parsing_spec.spl` - @pending/@skip

- Regex utils
  - `test/unit/app/tooling/regex_utils_spec.spl` - @pending

- Brief view
  - `test/unit/app/tooling/brief_view_spec.spl` - @pending

- Retry utils
  - `test/unit/app/tooling/retry_utils_spec.spl` - @pending

- JSON utils
  - `test/unit/app/tooling/json_utils_spec.spl` - @pending

- HTML utils
  - `test/unit/app/tooling/html_utils_spec.spl` - @pending

- Context pack
  - `test/unit/app/tooling/context_pack_spec.spl` - @pending/@skip

### Diagrams
- `test/unit/app/diagram/call_flow_profiling_spec.spl` - @pending
- `test/unit/app/diagram/filter_spec.spl` - @pending/@skip
- `test/unit/app/diagram/diagram_gen_spec.spl` - @pending/@skip

### Diagnostics
- `test/unit/app/diagnostics/text_formatter_spec.spl` - @pending

### Interpreter
- `test/unit/app/interpreter/debug_spec.spl` - @pending/@skip
- `test/unit/app/interpreter/class_method_call_spec.spl` - @pending
- `test/system/interpreter_bugs_spec.spl` - @skip

## 5. Domain-Specific Features

### Machine Learning
All ML tests are skipped:
- `test/unit/lib/ml/test_ffi_operator_spec.spl` - @skip
- `test/unit/lib/ml/fft_spec.spl` - @skip
- `test/unit/lib/ml/custom_autograd_spec.spl` - @skip
- `test/unit/lib/ml/simple_math_spec.spl` - @skip
- `test/unit/lib/ml/activation_spec.spl` - @skip

### Tensor Operations
- `test/feature/tensor_spec.spl` - @pending/@skip
- `test/feature/tensor_interface_spec.spl` - @pending
- `test/feature/tensor_bridge_spec.spl` - @pending
- Native backend implementation needed (factory.spl TODO)

### Math/Graphics
- **Vector3**
  - `test/feature/vec3_spec.spl` - @pending

- **Quaternion**
  - `test/feature/quat_spec.spl` - @pending

- **Matrix4x4**
  - `test/feature/mat4_spec.spl` - @pending

- **Transform**
  - `test/feature/transform_spec.spl` - @pending

- **Scene nodes**
  - `test/feature/scene_node_spec.spl` - @pending

- **Search/Index** (likely spatial)
  - `test/feature/search_spec.spl` - @pending/@skip
  - `test/feature/index_spec.spl` - @pending/@skip

### Physics Engine
All physics tests are pending/skipped:
- `test/unit/lib/physics/rigidbody_spec.spl` - @pending/@skip
- `test/unit/lib/physics/vector_spec.spl` - @pending/@skip
- `test/unit/lib/physics/materials_spec.spl` - @pending
- `test/unit/lib/physics/spatial_hash_spec.spl` - @pending/@skip
- `test/unit/lib/physics/contact_spec.spl` - @pending/@skip
- `test/unit/lib/physics/aabb_spec.spl` - @pending/@skip
- `test/unit/lib/physics/shapes_spec.spl` - @pending/@skip

### Game Engine
All game engine components are pending/skipped:
- `test/unit/lib/game_engine/material_spec.spl` - @pending
- `test/unit/lib/game_engine/actor_model_spec.spl` - @pending
- `test/unit/lib/game_engine/input_spec.spl` - @pending
- `test/unit/lib/game_engine/assets_spec.spl` - @pending
- `test/unit/lib/game_engine/physics_spec.spl` - @pending
- `test/unit/lib/game_engine/audio_spec.spl` - @pending
- `test/unit/lib/game_engine/component_spec.spl` - @pending/@skip
- `test/feature/component_spec.spl` - @pending

### GPU/Compute (Requires Hardware)
- **CUDA support**
  - 18 test cases in `test/feature/cuda_spec.spl` - @skip (requires_cuda tag)
  - FFI integration tests in test-simple/lib

- **Vulkan support**
  - 21 test cases in `test/feature/vulkan_spec.spl` - @skip (requires_vulkan tag)

- **Generic GPU**
  - 11 test cases in `test/feature/gpu_basic_spec.spl` - @skip (requires_gpu tag)
  - GPU intrinsics require kernel context (this.index()) - no surface syntax

Note: Tag-based test skipping (@tag) not supported on test cases

### LMS (Learning Management System)
- `test/unit/lib/lms/server_spec.spl` - @pending/@skip

### Database
- Database sync
  - `test/feature/database_sync_spec.spl` - @pending
  - Async operations pending (Task type needed)

- Contract persistence
  - `test/feature/contract_persistence_feature_spec.spl` - @pending/@skip

### Experiment Tracking
- `test/feature/experiment_tracking_spec.spl` - @pending
- `test/unit/std/exp/sweep_spec.spl` - @pending
- `test/unit/std/exp/run_spec.spl` - @pending
- `test/unit/std/exp/storage_spec.spl` - @pending
- `test/unit/std/exp/artifact_spec.spl` - @pending

### Other Domain Features
- Floor division (fdiv)
  - `test/feature/floor_division_fdiv_spec.spl` - @pending

- Shell API
  - `test/feature/shell_api_spec.spl` - @pending

- Fault detection
  - `test/feature/fault_detection_spec.spl` - @pending

- Static keyword
  - `test/feature/parser_static_keyword_spec.spl` - @pending

- Class invariants
  - `test/feature/class_invariant_spec.spl` - @pending

- Code quality tools
  - `test/feature/code_quality_tools_spec.spl` - @skip (no tests implemented)

- Bootstrap spec
  - `test/feature/bootstrap_spec.spl` - @skip

## 6. Embedded/Baremetal

### QEMU Support
- `test/unit/lib/qemu_spec.spl` - @skip (uses spawn keyword)
- QEMU availability checks in integration tests
- GDB integration for remote debugging

### Baremetal RISC-V
- Tests skip if binary not built
- Semihosting support implemented

## 7. Major TODOs by Category

### FFI Wrapper Migration
Many direct FFI calls need wrappers (from app.io or compiler.ffi):
- `time_now_unix_micros` - Used extensively
- `thread_sleep` - Sleep functionality
- `env_get` - Environment variables
- `file_*` operations - read_text, write_text, append_text, delete, exists
- `dir_*` operations - create, list
- `random_*` - uniform, randint

### Compiler TODOs
- Default trait methods implementation
- Native backend implementations (various)
- LLVM IR compilation (stub in bootstrap binary)
- Complex expression type inference in monomorphize
- HIR execution via instruction module
- Codegen via FFI to Rust

### Parser TODOs
- Proper exit implementation (package-dist.spl)
- Import analysis for unused functions
- Real regex compilation for custom blocks
- Real SQL parser for custom blocks
- Validation improvements

### Experiment/Config TODOs
- SdnValue type inspection
- rt_sdn_parse integration
- Config validation
- Artifact SDN parsing

### TreeSitter TODOs
- Position tracking in AST
- Parent tracking in node structure
- True incremental parsing with edit information

### Test Framework TODOs
- skip() doesn't halt execution in slow_it lambdas (BUG-RT)
- Return doesn't work in slow_it lambdas

## 8. Bootstrap Limitations

### Bootstrap Binary Issues
- `rt_compile_to_llvm_ir` is a stub (not implemented)
- Only bootstrap features available

### Runtime Limitations
- `rt_execute_native` hangs (unsafe group skipped)
- Min i64 literal too large for parser

## 9. System Tests

### Parser Improvements
- `test/system/parser_improvements_spec.spl` - @pending/@skip

### Feature Documentation
- `test/system/feature_doc_spec.spl` - @skip (uses await)

## 10. Command Not Implemented

These CLI commands are not implemented:
- Various commands in app/cli/dispatch.spl

## Summary Statistics

**Total @pending files:** ~80+
**Total @skip files:** ~100+
**Total TODO comments:** ~100+ (many FFI wrapper migrations)
**Total "not implemented" mentions:** ~50+

## Priority Areas (Suggested)

1. **High Priority:**
   - Async/await syntax completion
   - FFI wrapper creation (blocking many features)
   - LSP features (developer experience)
   - TreeSitter position tracking

2. **Medium Priority:**
   - ML/Tensor operations (if ML use cases are important)
   - Physics/Game engine (if game dev is a goal)
   - Package management
   - File I/O improvements

3. **Low Priority (Hardware Dependent):**
   - GPU/CUDA/Vulkan support (requires hardware)
   - QEMU integration (embedded use cases)

4. **Future/Nice-to-Have:**
   - Actor model
   - Verification with Lean 4
   - Advanced parser features (bitfield, set literals)
   - Game engine components
