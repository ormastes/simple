# 5-Phase Implementation Plan for Simple Language Features

This document outlines a phased approach to implementing the features identified in `needed_feature.md`.

## Phase 1: Foundation & Critical Infrastructure (Weeks 1-4)

**Goal:** Establish core infrastructure that unblocks other features

### 1.1 FFI Wrapper Migration (Priority: CRITICAL)
**Effort:** 2 weeks | **Blockers:** None | **Blocks:** Most runtime features

- [ ] Create wrapper module structure in `src/app/io/` or `src/compiler/ffi/`
- [ ] Implement time wrappers:
  - `time_now_unix_micros()` - Used extensively across codebase
  - `thread_sleep()` - Sleep functionality
- [ ] Implement file I/O wrappers:
  - `file_read_text()`, `file_write_text()`, `file_append_text()`
  - `file_exists()`, `file_delete()`
- [ ] Implement directory wrappers:
  - `dir_create()`, `dir_list()`
- [ ] Implement environment wrappers:
  - `env_get()` - Environment variables
- [ ] Implement random wrappers:
  - `random_uniform()`, `random_randint()`
- [ ] Update ~100+ call sites to use wrappers instead of direct FFI

**Success Criteria:**
- All direct FFI calls replaced with wrappers
- Wrappers tested and documented
- Experiment tracking tests can use new wrappers

### 1.2 Parser Critical Fixes (Priority: HIGH)
**Effort:** 1 week | **Blockers:** None | **Blocks:** Syntax features

- [ ] Fix match case inline array bug (`test/unit/compiler/match_empty_array_bug_spec.spl`)
- [ ] Fix `print()` return value (should return printed value, not nil)
- [ ] Fix runtime value syntax issues (nil identifier)
- [ ] Enable `skip()` to halt execution in slow_it lambdas (BUG-RT)
- [ ] Enable return in slow_it lambdas

**Success Criteria:**
- Parser bug tests pass
- Test framework properly handles skip/return

### 1.3 Basic Async Infrastructure (Priority: HIGH)
**Effort:** 1 week | **Blockers:** Parser fixes | **Blocks:** Async features

- [ ] Implement basic `async` keyword parsing
- [ ] Implement basic `await` keyword parsing
- [ ] Create Poll/Future core types
- [ ] Enable async function declarations
- [ ] Unblock: `test/unit/std/async_spec.spl`

**Success Criteria:**
- Simple async/await code compiles
- Basic async tests pass
- Foundation for coroutines established

### 1.4 Bootstrap Binary Improvements (Priority: MEDIUM)
**Effort:** 1 week | **Blockers:** None | **Blocks:** LLVM features

- [ ] Implement `rt_compile_to_llvm_ir` (currently stub)
- [ ] Fix `rt_execute_native` hanging issue
- [ ] Fix min i64 literal parsing

**Success Criteria:**
- Bootstrap binary can compile to LLVM IR
- Native execution works reliably

**Phase 1 Deliverables:**
- 100+ FFI wrappers migrated
- 5 critical parser bugs fixed
- Basic async/await support
- Improved bootstrap binary

---

## Phase 2: Core Language & Compiler Features (Weeks 5-10)

**Goal:** Complete essential language features and compiler capabilities

### 2.1 Syntax Features (Priority: HIGH)
**Effort:** 2 weeks | **Blockers:** Parser fixes | **Blocks:** Developer productivity

- [ ] **Set literals** `s{...}` - Rebuild runtime with new parser
  - Unblock: `test/feature/set_literal_spec.spl`
  - Unblock: `test/feature/custom_literal_spec.spl`
- [ ] **Bitfield syntax**
  - Unblock: `test/feature/bitfield_spec.spl`
- [ ] **Union types** (Issue #37)
- [ ] **Static keyword** support
  - Unblock: `test/feature/parser_static_keyword_spec.spl`

**Success Criteria:**
- All syntax feature tests pass
- Parser supports new syntax
- Runtime rebuilt with updated parser

### 2.2 Type System Enhancements (Priority: HIGH)
**Effort:** 3 weeks | **Blockers:** Phase 1 | **Blocks:** Advanced features

- [ ] **Effect inference and annotations**
  - Unblock: `test/feature/effect_annotations_spec.spl`
  - Unblock: `test/unit/compiler/effect_inference_spec.spl`
- [ ] **Advanced generics**
  - Unblock: `test/feature/generics_advanced_spec.spl`
  - Complex expression type inference in monomorphize
- [ ] **Default trait methods**
- [ ] **Class invariants**
  - Unblock: `test/feature/class_invariant_spec.spl`

**Success Criteria:**
- Effect system operational
- Advanced generic constraints work
- Trait system complete

### 2.3 TreeSitter Integration (Priority: MEDIUM)
**Effort:** 2 weeks | **Blockers:** None | **Blocks:** LSP features

- [ ] **Position tracking** - start_byte, end_byte, start_point, end_point
- [ ] **Parent/sibling navigation** - parent(), next_sibling(), prev_sibling()
- [ ] **Error tracking** - is_error()
- [ ] **Incremental parsing** - Edit information tracking
- [ ] Unblock 6 pending TreeSitter tests:
  - `treesitter_incremental_spec.spl`
  - `treesitter_error_recovery_spec.spl`
  - `treesitter_tree_real_spec.spl`
  - `treesitter_parser_real_spec.spl`
  - `treesitter_highlights_spec.spl`
  - `grammar_compile_spec.spl`

**Success Criteria:**
- Position tracking works
- Navigation works
- Incremental parsing functional
- All TreeSitter tests pass

### 2.4 Backend & Codegen (Priority: MEDIUM)
**Effort:** 3 weeks | **Blockers:** Type system | **Blocks:** Native compilation

- [ ] **Generator state machine codegen**
  - Unblock: `test/feature/generator_state_machine_codegen_spec.spl`
- [ ] **Linker integration**
  - Unblock: `test/unit/compiler/linker_spec.spl`
  - Unblock: `test/unit/compiler/linker_context_spec.spl`
  - Unblock: `test/unit/compiler/note_sdn_spec.spl`
- [ ] **JIT context improvements**
  - Unblock: `test/unit/compiler/jit_context_spec.spl`
- [ ] **Backend capabilities**
  - instruction_coverage_spec
  - exhaustiveness_validator_spec
  - differential_testing_spec
  - backend_capability_spec

**Success Criteria:**
- Generator codegen works
- Linker integration complete
- JIT context functional
- Backend tests pass

**Phase 2 Deliverables:**
- 4 major syntax features
- Complete type system with effects
- TreeSitter fully integrated
- Backend compilation improvements

---

## Phase 3: Standard Library & Runtime (Weeks 11-16)

**Goal:** Complete standard library and runtime features

### 3.1 Concurrency & Async (Priority: HIGH)
**Effort:** 3 weeks | **Blockers:** Phase 2 async | **Blocks:** Actor model

- [ ] **Complete async/await** - Full syntax support
  - Unblock: `test/feature/async_features_spec.spl`
  - Unblock: `test/unit/std/async_host_spec.spl`
  - Unblock: `test/unit/std/async_embedded_spec.spl`
- [ ] **Spawn keyword** - Thread/process support
  - Unblock: `test/unit/lib/qemu_spec.spl`
  - Unblock: `test/unit/std/console_basic_spec.spl`
  - Unblock: `test/unit/std/arc_spec.spl`
- [ ] **Stackless coroutines**
  - Unblock: `test/feature/stackless_coroutines_spec.spl`
- [ ] **Actor model/system**
  - Unblock: `test/feature/actors_spec.spl`
  - Unblock: `test/feature/actor_model_spec.spl`

**Success Criteria:**
- Async/await fully functional
- Thread spawning works
- Actor system operational
- 9+ async/concurrency tests pass

### 3.2 File I/O & System Integration (Priority: HIGH)
**Effort:** 2 weeks | **Blockers:** Phase 1 FFI wrappers | **Blocks:** Applications

- [ ] **Extended file I/O**
  - Unblock: `test/feature/file_io_extended_spec.spl`
  - Unblock: `test/system/file_io_spec.spl`
  - Unblock: `test/unit/std/infra/file_io_spec.spl`
  - Unblock: `test/unit/std/file_find_spec.spl`
- [ ] **Environment variables**
  - Unblock: `test/unit/std/env_spec.spl`
- [ ] **Process management**
  - Unblock: `test/unit/std/process_spec.spl`
- [ ] **System FFI**
  - Unblock: `test/unit/std/sys_ffi_spec.spl`
- [ ] **Resource limits**
  - Unblock: `test/unit/std/resource_limits_spec.spl`

**Success Criteria:**
- File I/O complete and tested
- Process management works
- System integration functional
- 9+ I/O tests pass

### 3.3 DateTime & Utilities (Priority: MEDIUM)
**Effort:** 1 week | **Blockers:** FFI wrappers | **Blocks:** Applications

- [ ] **DateTime functionality**
  - Unblock: `test/unit/std/datetime_spec.spl`
  - Unblock: `test/unit/std/datetime_ffi_spec.spl`
- [ ] **Logging**
  - Unblock: `test/unit/std/log_spec.spl`
- [ ] **Configuration**
  - Unblock: `test/unit/std/config_spec.spl`
  - Unblock: `test/unit/std/infra/config_env_spec.spl`

**Success Criteria:**
- DateTime operations work
- Logging framework functional
- Config system operational

### 3.4 Testing & Quality (Priority: MEDIUM)
**Effort:** 2 weeks | **Blockers:** None | **Blocks:** Developer productivity

- [ ] **Lexer FFI tests**
  - Unblock: `test/lib/std/compiler/lexer_ffi_test.spl`
- [ ] **Mock verification**
  - Unblock: `test/unit/std/mock_verification_spec.spl`
  - Unblock: `test/unit/std/mock_phase5_spec.spl`
  - Unblock: `test/unit/std/mock_phase6_spec.spl`
  - Unblock: `test/unit/std/mock_phase7_spec.spl`
- [ ] **Contract testing**
  - Unblock: `test/unit/std/contract_spec.spl`
- [ ] **Fuzzing support**
  - Unblock: `test/unit/std/fuzz_spec.spl`

**Success Criteria:**
- Testing framework complete
- Mock system functional
- Fuzzing operational

### 3.5 Dependency Injection & Database (Priority: LOW)
**Effort:** 1 week | **Blockers:** None | **Blocks:** Applications

- [ ] **Dependency injection**
  - Unblock: `test/unit/std/di_spec.spl`
- [ ] **Database integration**
  - Unblock: `test/unit/std/db_spec.spl`
  - Unblock: `test/feature/database_sync_spec.spl`
  - Unblock: `test/feature/contract_persistence_feature_spec.spl`

**Success Criteria:**
- DI framework works
- Database support functional

**Phase 3 Deliverables:**
- Complete async/concurrency support
- Full file I/O and system integration
- DateTime, logging, config systems
- Enhanced testing framework
- DI and database support

---

## Phase 4: Application & Developer Tools (Weeks 17-24)

**Goal:** Complete developer tooling and application features

### 4.1 LSP (Language Server Protocol) - PRIORITY
**Effort:** 4 weeks | **Blockers:** Phase 2 TreeSitter | **Blocks:** IDE integration

**Week 1-2: Core LSP Infrastructure**
- [ ] `test/unit/app/lsp/server_lifecycle_spec.spl` - Server startup/shutdown
- [ ] `test/unit/app/lsp/message_dispatcher_spec.spl` - Message routing
- [ ] `test/unit/app/lsp/document_sync_spec.spl` - Document synchronization

**Week 3: Navigation Features**
- [ ] `test/unit/app/lsp/definition_spec.spl` - Go to definition
- [ ] `test/unit/app/lsp/references_spec.spl` - Find references
- [ ] `test/unit/app/lsp/hover_spec.spl` - Hover information

**Week 4: Code Intelligence**
- [ ] `test/unit/app/lsp/completion_spec.spl` - Code completion
- [ ] `test/unit/app/lsp/diagnostics_spec.spl` - Error diagnostics
- [ ] Implement textDocument/codeAction handler

**Success Criteria:**
- LSP server operational
- All 8 LSP test suites pass
- IDE integration works (VS Code/etc)

### 4.2 Package Management (Priority: HIGH)
**Effort:** 2 weeks | **Blockers:** None | **Blocks:** Ecosystem growth

- [ ] **Semantic versioning**
  - Unblock: `test/unit/app/package/semver_spec.spl`
- [ ] **Package manifests**
  - Unblock: `test/unit/app/package/package_spec.spl`
  - Unblock: `test/unit/app/package/manifest_spec.spl`
- [ ] **Lock files**
  - Unblock: `test/unit/app/package/lockfile_spec.spl`
- [ ] **FFI package support**
  - Unblock: `test/unit/app/package/ffi_spec.spl`

**Success Criteria:**
- Package manager functional
- Dependency resolution works
- Package publishing/installation works

### 4.3 Debugger (DAP) Improvements (Priority: MEDIUM)
**Effort:** 1 week | **Blockers:** None | **Blocks:** Debugging experience

- [ ] Implement condition evaluation (currently returns false)
- [ ] Implement variable evaluation (currently returns error)
- [ ] Improve `test/unit/app/dap/server_hooks_integration_spec.spl`

**Success Criteria:**
- Conditional breakpoints work
- Variable inspection works
- DAP tests pass

### 4.4 Tooling & Utilities (Priority: MEDIUM)
**Effort:** 2 weeks | **Blockers:** None | **Blocks:** Developer productivity

- [ ] **Arg parsing** - `test/unit/app/tooling/arg_parsing_spec.spl`
- [ ] **Regex utils** - `test/unit/app/tooling/regex_utils_spec.spl`
- [ ] **JSON utils** - `test/unit/app/tooling/json_utils_spec.spl`
- [ ] **HTML utils** - `test/unit/app/tooling/html_utils_spec.spl`
- [ ] **Context pack** - `test/unit/app/tooling/context_pack_spec.spl`
- [ ] **Brief view** - `test/unit/app/tooling/brief_view_spec.spl`
- [ ] **Retry utils** - `test/unit/app/tooling/retry_utils_spec.spl`

**Success Criteria:**
- All 7 tooling test suites pass
- Utilities documented and usable

### 4.5 Diagrams & Diagnostics (Priority: LOW)
**Effort:** 1 week | **Blockers:** None | **Blocks:** Documentation/visualization

- [ ] **Call flow profiling** - `test/unit/app/diagram/call_flow_profiling_spec.spl`
- [ ] **Diagram filtering** - `test/unit/app/diagram/filter_spec.spl`
- [ ] **Diagram generation** - `test/unit/app/diagram/diagram_gen_spec.spl`
- [ ] **Text formatter** - `test/unit/app/diagnostics/text_formatter_spec.spl`

**Success Criteria:**
- Diagram generation works
- Diagnostics formatted nicely

**Phase 4 Deliverables:**
- Complete LSP implementation
- Package management system
- Enhanced debugger
- Developer tooling suite
- Diagram/diagnostic tools

---

## Phase 5: Domain-Specific Features (Weeks 25-32)

**Goal:** Complete domain-specific features for ML, graphics, physics, games

### 5.1 Math & Graphics Primitives (Priority: HIGH for graphics apps)
**Effort:** 2 weeks | **Blockers:** None | **Blocks:** Game engine, graphics apps

- [ ] **Vector3** - `test/feature/vec3_spec.spl`
- [ ] **Quaternion** - `test/feature/quat_spec.spl`
- [ ] **Matrix4x4** - `test/feature/mat4_spec.spl`
- [ ] **Transform** - `test/feature/transform_spec.spl`
- [ ] **Scene nodes** - `test/feature/scene_node_spec.spl`
- [ ] **Search/Index (spatial)**
  - `test/feature/search_spec.spl`
  - `test/feature/index_spec.spl`

**Success Criteria:**
- All math primitives implemented
- Scene graph works
- Spatial indexing functional

### 5.2 ML & Tensor Operations (Priority: HIGH for ML apps)
**Effort:** 3 weeks | **Blockers:** FFI wrappers | **Blocks:** ML applications

- [ ] **Tensor operations**
  - Unblock: `test/feature/tensor_spec.spl`
  - Unblock: `test/feature/tensor_interface_spec.spl`
  - Unblock: `test/feature/tensor_bridge_spec.spl`
  - Implement native backend (factory.spl TODO)
- [ ] **ML features**
  - Unblock: `test/unit/lib/ml/test_ffi_operator_spec.spl`
  - Unblock: `test/unit/lib/ml/fft_spec.spl`
  - Unblock: `test/unit/lib/ml/custom_autograd_spec.spl`
  - Unblock: `test/unit/lib/ml/simple_math_spec.spl`
  - Unblock: `test/unit/lib/ml/activation_spec.spl`

**Success Criteria:**
- Tensor operations work
- ML framework functional
- FFI integration with native backends

### 5.3 Physics Engine (Priority: MEDIUM for game dev)
**Effort:** 2 weeks | **Blockers:** Phase 5.1 math | **Blocks:** Game physics

- [ ] **Rigidbody** - `test/unit/lib/physics/rigidbody_spec.spl`
- [ ] **Vector** - `test/unit/lib/physics/vector_spec.spl`
- [ ] **Materials** - `test/unit/lib/physics/materials_spec.spl`
- [ ] **Spatial hash** - `test/unit/lib/physics/spatial_hash_spec.spl`
- [ ] **Contact** - `test/unit/lib/physics/contact_spec.spl`
- [ ] **AABB** - `test/unit/lib/physics/aabb_spec.spl`
- [ ] **Shapes** - `test/unit/lib/physics/shapes_spec.spl`

**Success Criteria:**
- Physics simulation works
- All 7 physics components tested
- Integration with game engine ready

### 5.4 Game Engine Components (Priority: MEDIUM for game dev)
**Effort:** 2 weeks | **Blockers:** Phase 5.1, 5.3 | **Blocks:** Game development

- [ ] **Material** - `test/unit/lib/game_engine/material_spec.spl`
- [ ] **Actor model** - `test/unit/lib/game_engine/actor_model_spec.spl`
- [ ] **Input** - `test/unit/lib/game_engine/input_spec.spl`
- [ ] **Assets** - `test/unit/lib/game_engine/assets_spec.spl`
- [ ] **Physics integration** - `test/unit/lib/game_engine/physics_spec.spl`
- [ ] **Audio** - `test/unit/lib/game_engine/audio_spec.spl`
- [ ] **Component system**
  - `test/unit/lib/game_engine/component_spec.spl`
  - `test/feature/component_spec.spl`

**Success Criteria:**
- All 7 game engine components work
- Basic game can be built
- ECS system functional

### 5.5 GPU/Compute Support (Priority: LOW - requires hardware)
**Effort:** 3 weeks | **Blockers:** Hardware availability | **Blocks:** GPU apps

**Note:** These require specific hardware and should be done last or in parallel if hardware is available.

- [ ] **Generic GPU** (11 tests)
  - Implement GPU intrinsics with kernel context
  - `test/feature/gpu_basic_spec.spl`

- [ ] **CUDA** (18 tests)
  - `test/feature/cuda_spec.spl`
  - CUDA toolkit integration

- [ ] **Vulkan** (21 tests)
  - `test/feature/vulkan_spec.spl`
  - Vulkan SDK integration

**Success Criteria:**
- GPU compute works on available hardware
- CUDA integration functional (if NVIDIA GPU available)
- Vulkan integration functional (if supported)

### 5.6 Other Domain Features (Priority: LOW)
**Effort:** 1 week | **Blockers:** Various | **Blocks:** Specific use cases

- [ ] **Floor division (fdiv)** - `test/feature/floor_division_fdiv_spec.spl`
- [ ] **Shell API** - `test/feature/shell_api_spec.spl`
- [ ] **Fault detection** - `test/feature/fault_detection_spec.spl`
- [ ] **Experiment tracking**
  - `test/feature/experiment_tracking_spec.spl`
  - `test/unit/std/exp/sweep_spec.spl`
  - `test/unit/std/exp/run_spec.spl`
  - `test/unit/std/exp/storage_spec.spl`
  - `test/unit/std/exp/artifact_spec.spl`
- [ ] **LMS (Learning Management)** - `test/unit/lib/lms/server_spec.spl`

**Success Criteria:**
- Domain-specific features work
- Experiment tracking functional

**Phase 5 Deliverables:**
- Complete math/graphics primitives
- ML/Tensor framework
- Physics engine (7 components)
- Game engine (7 components)
- GPU/Compute support (hardware-dependent)
- Misc domain features

---

## Verification & Advanced Features (Optional Phase 6)

These are advanced features that may be deferred:

### Lean 4 Verification Integration
- **Effort:** 4 weeks
- **Priority:** LOW (research/advanced use cases)
- Currently returns empty results with warning
- Requires Lean 4 toolchain integration

### Macro System
- **Effort:** 3 weeks
- **Priority:** LOW (metaprogramming)
- `test/system/macro_consteval_simple_spec.spl`

### QEMU & Embedded Integration
- **Effort:** 2 weeks
- **Priority:** LOW (embedded use cases)
- `test/unit/lib/qemu_spec.spl`
- GDB integration, remote debugging

---

## Implementation Strategy

### Multi-Agent Approach

**Phase 1:** 3-4 agents working in parallel
- Agent 1: FFI wrapper migration
- Agent 2: Parser fixes
- Agent 3: Async infrastructure
- Agent 4: Bootstrap improvements

**Phase 2:** 4 agents
- Agent 1: Syntax features
- Agent 2: Type system
- Agent 3: TreeSitter
- Agent 4: Backend/codegen

**Phase 3:** 3-4 agents
- Agent 1: Concurrency & async
- Agent 2: File I/O & system
- Agent 3: DateTime & utilities
- Agent 4: Testing & quality

**Phase 4:** 3 agents
- Agent 1: LSP (largest effort)
- Agent 2: Package management
- Agent 3: Tooling & debugger

**Phase 5:** 3-4 agents
- Agent 1: Math & graphics
- Agent 2: ML & tensors
- Agent 3: Physics engine
- Agent 4: Game engine

### Testing Strategy

- Each feature must have passing tests before PR
- Integration tests after each phase
- Performance benchmarks for critical paths
- Documentation updated alongside code

### Risk Management

**High Risk:**
- FFI wrapper migration (touches 100+ files)
- Async/await implementation (complex)
- LSP implementation (large surface area)

**Mitigation:**
- Incremental migration with backwards compatibility
- Extensive testing at each step
- Early feedback from users

**Dependencies:**
- Phase 2 depends on Phase 1 (async, FFI)
- Phase 3 depends on Phase 1 (FFI wrappers)
- Phase 4 depends on Phase 2 (TreeSitter for LSP)
- Phase 5 depends on Phase 1, 3 (FFI, runtime features)

---

## Success Metrics

**Phase 1:**
- 100+ FFI sites migrated
- 5 parser bugs fixed
- 80% of Phase 1 tests passing

**Phase 2:**
- 4 syntax features complete
- Type system with effects working
- 90% of Phase 2 tests passing

**Phase 3:**
- Full async/concurrency support
- Complete I/O system
- 95% of Phase 3 tests passing

**Phase 4:**
- LSP fully functional
- Package manager operational
- 100% of Phase 4 tests passing

**Phase 5:**
- Math/graphics complete
- ML framework operational
- Physics/game engine functional
- 90% of Phase 5 tests passing (hardware-dependent tests may be skipped)

**Overall:**
- Reduce @skip tests from 100+ to <20 (hardware-dependent only)
- Reduce @pending tests from 80+ to 0
- All TODOs resolved or tracked in issues
- No stub implementations remaining

---

## Timeline Summary

| Phase | Duration | Agents | Key Deliverables |
|-------|----------|--------|------------------|
| Phase 1 | 4 weeks | 3-4 | FFI wrappers, Parser fixes, Basic async |
| Phase 2 | 6 weeks | 4 | Syntax, Type system, TreeSitter, Backend |
| Phase 3 | 6 weeks | 3-4 | Async complete, I/O, Runtime features |
| Phase 4 | 8 weeks | 3 | LSP, Package mgmt, Tooling |
| Phase 5 | 8 weeks | 3-4 | ML, Physics, Game engine, GPU |
| **Total** | **32 weeks** | **~8 months** | **Complete feature set** |

---

## Next Steps

1. Review and approve this plan
2. Set up agent coordination infrastructure
3. Begin Phase 1 with 3-4 parallel agents
4. Establish CI/CD for continuous testing
5. Weekly sync meetings to track progress
6. Adjust timeline based on actual progress
