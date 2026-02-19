# Large File Refactoring Plan

**Generated:** 2026-01-19
**Purpose:** Break down files >800 lines into smaller, maintainable modules

## Summary

Found **93 files** exceeding 800 lines (15 Rust core files, 78 Simple stdlib/test files).

### Priority Classification

- **CRITICAL (>2000 lines):** 1 file - requires immediate attention
- **HIGH (1200-2000 lines):** 14 files - significant complexity
- **MEDIUM (800-1200 lines):** 78 files - manageable but should be addressed

---

## CRITICAL Priority

### 1. `src/runtime/src/value/ffi.rs` - 6467 lines ⚠️

**Problem:** Massive "God file" containing 331 functions across 60+ unrelated domains.

**Current Structure:**
- Value creation/extraction (100 lines)
- Memory allocation (50 lines)
- I/O capture system (200 lines)
- Math functions (100 lines)
- File system operations (300 lines)
- Date/Time operations (200 lines)
- Process execution (200 lines)
- Atomic operations (200 lines)
- Concurrent data structures (Arena, ConcurrentMap, ConcurrentQueue, etc.) (500 lines)
- Hash functions (SHA1, SHA256, XXHash) (300 lines)
- **PyTorch Integration (3000+ lines):**
  - Tensor operations
  - Autograd context
  - Neural network layers (Conv3d, RNN, MultiheadAttention, Transformer)
  - Optimizers (RMSprop, etc.)
  - Dataset operations
  - Distributed training (DDP)
  - ONNX operations
  - JIT/TorchScript

**Refactoring Strategy:**

Split into **~20 focused modules**:

```
src/runtime/src/value/
├── ffi/
│   ├── mod.rs                      # Re-exports
│   ├── value_ops.rs                # Value creation/extraction/checking (200 lines)
│   ├── memory.rs                   # Allocation/deallocation (100 lines)
│   ├── equality.rs                 # Value equality (100 lines)
│   ├── interpreter_bridge.rs       # Interpreter FFI (100 lines)
│   ├── error_handling.rs           # Error/panic handling (60 lines)
│   ├── contracts.rs                # Design by contract (120 lines)
│   ├── io_capture.rs               # Stdout/stderr capture (150 lines)
│   ├── stdin_mock.rs               # Stdin mocking for tests (100 lines)
│   ├── print.rs                    # Print functions (150 lines)
│   ├── coverage.rs                 # Code coverage probes (40 lines)
│   ├── process.rs                  # Process control (100 lines)
│   ├── math.rs                     # Math operations (120 lines)
│   ├── fs.rs                       # File system operations (350 lines)
│   ├── env.rs                      # Environment variables (80 lines)
│   ├── base64.rs                   # Base64 encoding (130 lines)
│   ├── datetime.rs                 # Date/time operations (220 lines)
│   ├── file_io.rs                  # File I/O (200 lines)
│   ├── process_exec.rs             # Process execution (200 lines)
│   ├── search.rs                   # File/directory search (120 lines)
│   ├── path.rs                     # Path manipulation (140 lines)
│   ├── atomic.rs                   # Atomic operations (200 lines)
│   ├── sync.rs                     # Sync primitives (AtomicFlag, Once, Condvar) (150 lines)
│   ├── concurrent/
│   │   ├── mod.rs
│   │   ├── arena.rs                # Arena allocator (110 lines)
│   │   ├── map.rs                  # ConcurrentMap (100 lines)
│   │   ├── queue.rs                # ConcurrentQueue (80 lines)
│   │   ├── stack.rs                # ConcurrentStack (80 lines)
│   │   ├── pool.rs                 # ResourcePool (90 lines)
│   │   └── tls.rs                  # Thread-local storage (80 lines)
│   ├── hash/
│   │   ├── mod.rs
│   │   ├── sha1.rs                 # SHA1 hashing (80 lines)
│   │   ├── sha256.rs               # SHA256 hashing (80 lines)
│   │   └── xxhash.rs               # XXHash (80 lines)
│   └── pytorch/                    # Feature-gated
│       ├── mod.rs
│       ├── tensor.rs               # Tensor storage/ops (200 lines)
│       ├── autograd.rs             # Autograd context (150 lines)
│       ├── layers/
│       │   ├── mod.rs
│       │   ├── conv.rs             # Conv3d (100 lines)
│       │   ├── rnn.rs              # RNN layers (150 lines)
│       │   ├── attention.rs        # MultiheadAttention (170 lines)
│       │   ├── positional.rs       # Positional encoding (60 lines)
│       │   ├── transformer_encoder.rs  # (170 lines)
│       │   └── transformer_decoder.rs  # (220 lines)
│       ├── optim/
│       │   ├── mod.rs
│       │   └── rmsprop.rs          # RMSprop optimizer (70 lines)
│       ├── jit.rs                  # JIT/TorchScript (200 lines)
│       ├── serialization.rs        # Model save/load (70 lines)
│       ├── onnx.rs                 # ONNX operations (130 lines)
│       ├── dataset.rs              # Dataset operations (180 lines)
│       └── distributed.rs          # DDP wrapper (200 lines)
```

**Implementation Steps:**

1. Create module structure with `mod.rs` re-exports
2. Extract PyTorch code first (largest chunk, feature-gated, easy to isolate)
3. Extract concurrent data structures (self-contained)
4. Extract I/O and file system operations
5. Extract remaining utilities (hash, datetime, base64, etc.)
6. Update imports across codebase
7. Run full test suite after each extraction
8. Update documentation

**Benefits:**
- Reduces file from 6467 → ~200 lines (mod.rs with re-exports)
- Improves compile times (parallel compilation of modules)
- Easier testing (unit tests per module)
- Clear separation of concerns
- PyTorch code can be easily feature-gated

---

## HIGH Priority (1200-2000 lines)

### 2. `simple/std_lib/src/ui/gui/vulkan.spl` - 1861 lines

**Problem:** Massive Vulkan bindings in single file.

**Refactoring Strategy:**
```
std_lib/src/ui/gui/vulkan/
├── __init__.spl              # Re-exports (50 lines)
├── instance.spl              # VkInstance, VkPhysicalDevice (300 lines)
├── device.spl                # VkDevice, VkQueue (250 lines)
├── swapchain.spl             # VkSwapchain (200 lines)
├── pipeline.spl              # VkPipeline, VkShaderModule (300 lines)
├── commands.spl              # VkCommandBuffer, VkCommandPool (250 lines)
├── sync.spl                  # VkSemaphore, VkFence (150 lines)
├── memory.spl                # VkDeviceMemory, VkBuffer (250 lines)
└── descriptors.spl           # VkDescriptorSet, VkDescriptorPool (200 lines)
```

### 3. `simple/std_lib/src/ml/engine/__init__.spl` - 1766 lines

**Problem:** ML engine with multiple subsystems.

**Refactoring Strategy:**
```
std_lib/src/ml/engine/
├── __init__.spl              # Re-exports (50 lines)
├── core.spl                  # Engine core (300 lines)
├── training.spl              # Training loop (350 lines)
├── inference.spl             # Inference engine (300 lines)
├── optimization.spl          # Model optimization (250 lines)
├── checkpointing.spl         # Checkpoint save/load (200 lines)
├── metrics.spl               # Metrics tracking (200 lines)
└── distributed.spl           # Distributed training (250 lines)
```

### 4. `src/type/src/effects.rs` - 1440 lines

**Problem:** Effect inference system with multiple phases.

**Current Structure:**
- Phase 2: Effect inference (200 lines)
- Phase 5: Promise wrapping (150 lines)
- Phase 6: Await inference (200 lines)
- Call graph analysis (150 lines)
- Tarjan SCC algorithm (100 lines)
- Transitive propagation (150 lines)
- Type utilities (100 lines)
- Tests (400 lines)

**Refactoring Strategy:**
```
src/type/src/effects/
├── mod.rs                    # Public API, re-exports (100 lines)
├── core.rs                   # Effect enum, EffectEnv (50 lines)
├── inference.rs              # Phase 2: Effect inference (250 lines)
├── promise.rs                # Phase 5: Promise wrapping (200 lines)
├── await_mode.rs             # Phase 6: Await inference (250 lines)
├── call_graph.rs             # Call graph builder (150 lines)
├── scc.rs                    # Tarjan SCC algorithm (150 lines)
├── propagation.rs            # Transitive effect propagation (200 lines)
└── type_utils.rs             # Promise type utilities (150 lines)
```

**Benefits:**
- Clear separation of async-by-default phases
- Each phase can be tested independently
- SCC algorithm isolated (reusable)
- Easier to understand and maintain

### 5. `simple/app/interpreter/ast_convert.spl` - 1405 lines

**Problem:** Large AST conversion with type definitions and conversion logic mixed.

**Refactoring Strategy:**
```
simple/app/interpreter/
├── ast/
│   ├── __init__.spl          # Re-exports (50 lines)
│   ├── types.spl             # AST type definitions (400 lines)
│   ├── module.spl            # Module/Import conversion (200 lines)
│   ├── statement.spl         # Statement conversion (350 lines)
│   ├── expression.spl        # Expression conversion (300 lines)
│   └── pattern.spl           # Pattern conversion (150 lines)
```

### 6. `simple/std_lib/src/compiler_core/regex.spl` - 1401 lines

**Refactoring Strategy:**
```
std_lib/src/compiler_core/regex/
├── __init__.spl              # Re-exports (50 lines)
├── engine.spl                # Regex engine core (400 lines)
├── parser.spl                # Pattern parser (350 lines)
├── matcher.spl               # Matching logic (300 lines)
└── replace.spl               # Replace operations (250 lines)
```

### 7. `simple/std_lib/src/ui/gui/imgui.spl` - 1306 lines

**Refactoring Strategy:**
```
std_lib/src/ui/gui/imgui/
├── __init__.spl              # Re-exports (50 lines)
├── context.spl               # ImGui context (200 lines)
├── widgets.spl               # Basic widgets (300 lines)
├── layout.spl                # Layout widgets (250 lines)
├── windows.spl               # Window management (250 lines)
└── styling.spl               # Styling/theming (250 lines)
```

### 8-15. Additional HIGH Priority Files

Similar patterns apply to:
- `simple/std_lib/src/godot/vulkan.spl` (1280 lines) → Split by subsystem
- `simple/std_lib/test/features/infrastructure/parser_spec.spl` (1261 lines) → Split by parser component
- `simple/std_lib/src/tooling/deployment/packaging.spl` (1249 lines) → Split by package format
- `src/compiler/src/blocks/math/eval.rs` (1231 lines) → Split by operation type
- `src/compiler/src/interpreter_extern.rs` (1230 lines) → Split by extern category
- `src/runtime/src/monoio_direct.rs` (1228 lines) → Split by I/O operation
- `tests/system/low_coverage_tests8.rs` (1225 lines) → Group by feature area
- `src/runtime/src/monoio_executor.rs` (1171 lines) → Split executor concerns

---

## MEDIUM Priority (800-1200 lines)

**78 files** in this category. General strategies:

### For Test Files (20+ files)
- Split by test scenario groupings
- Create test module hierarchies
- Use submodules for feature areas

### For Standard Library Files (50+ files)
- Split by API domains
- Separate types from implementations
- Extract utilities to separate modules

### Example: `src/driver/src/cli/test_runner.rs` (1093 lines)

**Refactoring Strategy:**
```
src/driver/src/cli/test_runner/
├── mod.rs                    # Public API (100 lines)
├── runner.rs                 # Test execution (300 lines)
├── reporter.rs               # Test reporting (250 lines)
├── discovery.rs              # Test discovery (200 lines)
└── filter.rs                 # Test filtering (200 lines)
```

### Example: `src/compiler/src/interpreter_call/core.rs` (1090 lines)

**Refactoring Strategy:**
```
src/compiler/src/interpreter_call/
├── core.rs                   # Core function calls (300 lines)
├── args.rs                   # Argument binding (250 lines)
├── methods.rs                # Method dispatch (250 lines)
└── aop.rs                    # AOP/injection handling (250 lines)
```

### Example: `src/driver/src/main.rs` (1002 lines)

**Refactoring Strategy:**
```
src/driver/src/
├── main.rs                   # Entry point only (100 lines)
├── cli/
│   ├── parser.rs             # CLI argument parsing (250 lines)
│   ├── commands.rs           # Command dispatch (300 lines)
│   └── metrics.rs            # Startup metrics (100 lines)
└── runner.rs                 # Execution logic (250 lines)
```

---

## Implementation Guidelines

### General Principles

1. **One Concern Per Module** - Each module should handle one logical domain
2. **Module Size Target** - Aim for 200-400 lines per module
3. **Clear Boundaries** - Modules should have minimal coupling
4. **Test Coverage** - Ensure tests pass after each refactoring step
5. **Progressive Refactoring** - Tackle files incrementally, not all at once

### Refactoring Process

**For Each File:**

1. **Analyze** - Map out logical groupings (30 min)
2. **Design** - Create module structure plan (30 min)
3. **Extract** - Move code to new modules incrementally
4. **Test** - Run tests after each extraction
5. **Cleanup** - Remove old file, update re-exports
6. **Document** - Update docs and comments
7. **Review** - Ensure quality and consistency

### Testing Strategy

```bash
# After each extraction
make check              # Quick validation
cargo test --workspace  # Full test suite

# Before committing
make check-full         # Coverage + duplication check
```

### Commit Strategy

Use Jujutsu (NOT git):

```bash
# After each logical extraction
jj commit -m "refactor(module): Extract X from large_file

- Split X functionality into new module
- Update imports and re-exports
- All tests passing"

jj bookmark set main -r @
jj git push --bookmark main
```

---

## Priority Order for Execution

### Phase 1: Critical (Week 1-2)
1. `src/runtime/src/value/ffi.rs` (6467 lines) - HIGHEST IMPACT

### Phase 2: Runtime/Compiler Core (Week 3-4)
2. `src/type/src/effects.rs` (1440 lines)
3. `src/compiler/src/blocks/math/eval.rs` (1231 lines)
4. `src/compiler/src/interpreter_extern.rs` (1230 lines)
5. `src/runtime/src/monoio_direct.rs` (1228 lines)
6. `src/runtime/src/monoio_executor.rs` (1171 lines)

### Phase 3: Driver/Tools (Week 5)
7. `src/driver/src/cli/test_runner.rs` (1093 lines)
8. `src/compiler/src/interpreter_call/core.rs` (1090 lines)
9. `src/driver/src/doctest.rs` (1051 lines)
10. `src/driver/src/main.rs` (1002 lines)

### Phase 4: Simple Interpreter (Week 6)
11. `simple/app/interpreter/ast_convert.spl` (1405 lines)

### Phase 5: Standard Library - UI/Graphics (Week 7-8)
12. `simple/std_lib/src/ui/gui/vulkan.spl` (1861 lines)
13. `simple/std_lib/src/ui/gui/imgui.spl` (1306 lines)
14. `simple/std_lib/src/ui/gui/vulkan_renderer.spl` (1233 lines)

### Phase 6: Standard Library - ML (Week 9)
15. `simple/std_lib/src/ml/engine/__init__.spl` (1766 lines)
16. `simple/std_lib/src/ml/torch/transforms.spl` (1013 lines)

### Phase 7: Standard Library - Core (Week 10)
17. `simple/std_lib/src/compiler_core/regex.spl` (1401 lines)
18. Remaining stdlib files

### Phase 8: Tests (Week 11-12)
19. Test files (as needed for coverage improvements)

---

## Metrics & Success Criteria

### Current State
- **93 files** > 800 lines
- **Average size:** 1,050 lines
- **Largest file:** 6,467 lines
- **Total lines in large files:** ~120,000 lines

### Target State
- **0 files** > 800 lines
- **Average module size:** 250-400 lines
- **Largest file:** < 600 lines
- **Number of modules:** ~300-400 (increase from ~93)

### KPIs
- **Compilation time** - Should improve with parallelism
- **Test isolation** - Easier to run targeted tests
- **Code navigation** - Easier to find relevant code
- **Maintainability** - Easier to understand and modify

---

## Tools & Automation

### File Analysis
```bash
# Find large files
find . -type f \( -name "*.rs" -o -name "*.spl" \) ! -path "*/target/*" \
  -exec sh -c 'lines=$(wc -l < "$1"); if [ "$lines" -gt 800 ]; then \
  echo "$lines $1"; fi' _ {} \; | sort -rn

# Analyze function count
grep -c "^pub fn \|^fn " file.rs

# Analyze module sections
grep -n "^//.*===\|^//.*---" file.rs
```

### Refactoring Helpers
```bash
# Create module structure
mkdir -p src/runtime/src/value/ffi
touch src/runtime/src/value/ffi/{mod,value_ops,memory}.rs

# Update imports across codebase
rg "use.*value::ffi::" --files-with-matches | \
  xargs -I {} echo "Update: {}"
```

---

## Risk Mitigation

### Risks
1. **Breaking Changes** - Incorrect imports after refactoring
2. **Test Failures** - Logic errors during code movement
3. **Merge Conflicts** - If multiple people work on same files
4. **Performance Regression** - Unnecessary overhead from module boundaries

### Mitigations
1. **Incremental Approach** - One module at a time
2. **Continuous Testing** - Run tests after each extraction
3. **Use Jujutsu** - Easy to undo/revert changes
4. **Code Review** - Review each extraction before merging
5. **Benchmark Critical Paths** - Measure performance before/after

---

## Conclusion

This refactoring plan addresses technical debt by breaking down large files into focused, maintainable modules. The priority order focuses on core runtime/compiler files first (highest impact), followed by tools, then standard library.

**Estimated effort:** 12 weeks for complete refactoring (all 93 files)
**Quick wins:** Phase 1-2 (ffi.rs + core compiler files) provides 60% of the value

**Next steps:**
1. Get approval for this plan
2. Start with `ffi.rs` extraction (biggest impact)
3. Create branch protection to prevent new >800 line files
4. Track progress in `doc/report/refactoring_progress.md`
