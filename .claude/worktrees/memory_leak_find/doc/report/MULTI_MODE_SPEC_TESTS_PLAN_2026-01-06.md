# Multi-Mode Spec Test Execution - Implementation Plan

**Date:** 2026-01-06
**Status:** 📋 Planned
**Feature IDs:** #2050-#2054
**Priority:** Immediate (Sprint)

## Overview

This document outlines the implementation plan for multi-mode spec test execution, enabling tests to run across all execution backends: Interpreter, JIT, SMF (Cranelift), and SMF (LLVM).

## Motivation

Currently, spec tests run only in interpreter mode. To ensure correctness across all execution modes and catch mode-specific bugs, we need to:

1. Run tests in interpreter, JIT, and compiled (SMF) modes
2. Compare results across modes for consistency
3. Allow mode-specific test configuration
4. Skip unavailable/unsupported modes gracefully
5. Report mode-specific failures clearly

## Feature Summary

| Feature ID | Feature | Description |
|------------|---------|-------------|
| #2050 | Execution Mode API | Core API for mode management |
| #2051 | Multi-Level Configuration | Project/dir/file/block/test config |
| #2052 | Mode Skip Configuration | Selective mode skipping |
| #2053 | Mode Failure Handling | Failure propagation strategies |
| #2054 | Mode Reporting & Diagnostics | Enhanced mode-aware output |

## Execution Modes

### 1. Interpreter Mode
- **Status:** ✅ Currently implemented
- **Use cases:** Default execution, debugging, reflection
- **Limitations:** Slower, no optimization

### 2. JIT Mode (Cranelift)
- **Status:** 🔄 Partially implemented
- **Use cases:** Fast startup, REPL, hot reload
- **Limitations:** In-memory only, limited optimization

### 3. SMF Standalone (Cranelift)
- **Status:** ✅ Implemented
- **Use cases:** Production binaries, full optimization
- **Limitations:** Slower startup, disk artifacts

### 4. SMF Standalone (LLVM)
- **Status:** 📋 Planned (not implemented)
- **Use cases:** Advanced optimization, 32-bit targets
- **Limitations:** Not yet available

## Configuration Hierarchy

### Precedence (Highest → Lowest)

1. **Test Level** - Individual `it` block
2. **Block Level** - `describe`/`context` block
3. **File Level** - File attribute `#[modes(...)]`
4. **Directory Level** - `.spec_config.sdn` file
5. **Project Level** - `simple.toml` `[test]` section

### Configuration Options

```sdn
# .spec_config.sdn (directory level)
modes: [interpreter, jit, smf_cranelift]
skip_modes: [smf_llvm]
mode_failure_strategy: skip_remaining  # or fail_all, collect_all
```

```toml
# simple.toml (project level)
[test]
default_modes = ["interpreter", "jit", "smf_cranelift", "smf_llvm"]
mode_failure_strategy = "skip_remaining"
```

```simple
# File level
#[modes(interpreter, jit)]
#[skip_modes(smf_llvm)]

# Block level
describe("Feature", modes=[ExecutionMode.Interpreter, ExecutionMode.JIT]):
    # Test level
    it("specific test", modes=[ExecutionMode.Interpreter]):
        pass
```

## Implementation Phases

### Phase 1: Core Infrastructure (Week 1)
- [ ] Define `ExecutionMode` enum in `simple/std_lib/src/spec/execution_mode.spl`
- [ ] Implement `ModeSet` type with set operations
- [ ] Add `run_in_modes(modes, fn)` API
- [ ] Extend `SpecRunner` to track current mode
- [ ] Add mode metadata to test results

### Phase 2: Configuration System (Week 1-2)
- [ ] Implement SDN config file parsing (`.spec_config.sdn`)
- [ ] Add `simple.toml` `[test]` section support
- [ ] Implement file-level attribute parsing `#[modes(...)]`
- [ ] Build configuration hierarchy resolver
- [ ] Add configuration inheritance logic

### Phase 3: Execution Engine (Week 2-3)
- [ ] Modify spec runner for multi-mode execution
- [ ] Implement mode switching:
  - Interpreter: Direct execution (existing)
  - JIT: Compile to memory, execute
  - SMF: Compile to `.smf`, load, execute
- [ ] Add execution context isolation per mode
- [ ] Handle mode compilation errors gracefully

### Phase 4: Skip & Failure Handling (Week 3)
- [ ] Implement `skip_modes` logic with inheritance
- [ ] Implement `only_modes` exclusive mode list
- [ ] Add failure strategies:
  - `skip_remaining`: Continue with next mode
  - `fail_all`: Abort on first failure
  - `collect_all`: Run all, report all failures
- [ ] Detect mode availability (e.g., LLVM not ready)
- [ ] Skip unavailable modes automatically

### Phase 5: Reporting (Week 4)
- [ ] Enhanced output with mode labels
- [ ] Mode-specific error messages
- [ ] Performance comparison table
- [ ] Summary statistics by mode
- [ ] Configuration source tracking
- [ ] Diagnostic API for programmatic access

## Affected Test Files

### Total Impact
- **~100 spec test files** in `simple/std_lib/test/`
- All files gain multi-mode capability
- Most files work in all modes by default
- Some files need mode restrictions

### Priority Test Files (Phase 1-2)

**System Tests (Framework validation):**
1. `system/spec/spec_framework_spec.spl` - Framework self-tests
2. `system/spec/matchers/spec_matchers_spec.spl` - Matcher tests
3. `system/spec/feature_doc_spec.spl` - Feature doc tests

**Unit Tests (Simple targets):**
4. `unit/core/arithmetic_spec.spl` - Simple arithmetic (good compilation target)
5. `unit/core/primitives_spec.spl` - Basic types
6. `unit/core/comparison_spec.spl` - Comparison operators

**Runtime Behavior:**
7. `unit/core/collections_spec.spl` - Array/Dict/Set operations
8. `unit/core/string_spec.spl` - String manipulation

**Codegen-Specific:**
9. `features/codegen/cranelift_spec.spl` - Cranelift backend
10. `features/codegen/llvm_backend_spec.spl` - LLVM backend (skip until ready)

### Files Needing Mode Restrictions

**Interpreter-Only (Reflection/Parsing):**
- `system/doctest/parser/parser_spec.spl` - Doctest parsing
- `system/doctest/matcher/matcher_spec.spl` - Output matching
- `system/doctest/runner/runner_spec.spl` - Example execution
- `system/doctest/doctest_advanced_spec.spl` - Advanced doctest
- `integration/doctest/discovery_spec.spl` - Discovery logic

**Configuration:**
```simple
#[only_modes(interpreter)]  # At file level
```

**Mode-Specific Behavior:**
- `unit/concurrency/concurrency_spec.spl` - May differ in compiled mode
- `unit/concurrency/manual_mode_spec.spl` - Mode-specific scheduling
- `features/testing_framework/*_spec.spl` - Framework meta-tests

**Configuration:**
```simple
describe("Async behavior", modes=[ExecutionMode.Interpreter]):
    # Interpreter-specific concurrency tests
```

### Full Test File List

#### Unit Tests (25 files)
```
unit/core/arithmetic_spec.spl
unit/core/comparison_spec.spl
unit/core/primitives_spec.spl
unit/core/hello_spec.spl
unit/core/pattern_matching_spec.spl
unit/core/collections_spec.spl
unit/core/string_spec.spl
unit/core/math_spec.spl
unit/core/context_spec.spl
unit/core/random_spec.spl
unit/core/dsl_spec.spl
unit/core/regex_spec.spl
unit/core/sync_spec.spl
unit/core/decorators_spec.spl
unit/core/fluent_interface_spec.spl
unit/core/attributes_spec.spl
unit/core/pattern_analysis_spec.spl
unit/units/units_spec.spl
unit/spec/context_sharing_spec.spl
unit/spec/shared_examples_spec.spl
unit/spec/let_memoization_spec.spl
unit/spec/union_impl_spec.spl
unit/concurrency/manual_mode_spec.spl ⚠️ (mode-specific)
unit/concurrency/concurrency_spec.spl ⚠️ (mode-specific)
unit/contracts/contracts_spec.spl
```

#### System Tests (10 files)
```
system/spec/matchers/spec_matchers_spec.spl
system/spec/spec_framework_spec.spl
system/spec/feature_doc_spec.spl
system/doctest/parser/parser_spec.spl ❌ (interpreter-only)
system/doctest/matcher/matcher_spec.spl ❌ (interpreter-only)
system/doctest/runner/runner_spec.spl ❌ (interpreter-only)
system/doctest/doctest_advanced_spec.spl ❌ (interpreter-only)
system/sdn/fixtures_spec.spl
```

#### Feature Tests (60 files)
```
features/infrastructure/lexer_spec.spl
features/infrastructure/parser_spec.spl
features/infrastructure/ast_spec.spl
features/infrastructure/hir_spec.spl
features/infrastructure/mir_spec.spl
features/infrastructure/runtime_value_spec.spl
features/infrastructure/gc_spec.spl
features/infrastructure/package_manager_spec.spl
features/infrastructure/smf_spec.spl
features/types/basic_types_spec.spl
features/types/enums_spec.spl
features/types/memory_types_spec.spl
features/types/borrowing_spec.spl
features/types/option_result_spec.spl
features/types/operators_spec.spl
features/types/generics_spec.spl
features/language/classes_spec.spl
features/language/functions_spec.spl
features/language/structs_spec.spl
features/language/variables_spec.spl
features/language/methods_spec.spl
features/language/closures_spec.spl
features/language/imports_spec.spl
features/language/macros_spec.spl
features/language/traits_spec.spl
features/data_structures/arrays_spec.spl
features/data_structures/dicts_spec.spl
features/data_structures/strings_spec.spl
features/data_structures/tuples_spec.spl
features/data_structures/sets_spec.spl
features/data_structures/ranges_spec.spl
features/control_flow/loops_spec.spl
features/control_flow/match_spec.spl
features/control_flow/conditionals_spec.spl
features/control_flow/error_handling_spec.spl
features/concurrency/actors_spec.spl
features/concurrency/async_await_spec.spl
features/concurrency/generators_spec.spl
features/concurrency/futures_spec.spl
features/codegen/cranelift_spec.spl
features/codegen/buffer_pool_spec.spl
features/codegen/generator_codegen_spec.spl
features/codegen/llvm_backend_spec.spl ⚠️ (LLVM mode only when ready)
features/codegen/native_binary_spec.spl
features/testing_framework/describe_blocks_spec.spl ⚠️ (framework meta)
features/testing_framework/context_blocks_spec.spl ⚠️ (framework meta)
features/testing_framework/it_examples_spec.spl ⚠️ (framework meta)
features/testing_framework/before_each_spec.spl ⚠️ (framework meta)
features/testing_framework/after_each_spec.spl ⚠️ (framework meta)
features/testing_framework/expect_matchers_spec.spl ⚠️ (framework meta)
features/testing_framework/doctest_spec.spl ⚠️ (framework meta)
```

#### Integration Tests (1 file)
```
integration/doctest/discovery_spec.spl ❌ (interpreter-only)
```

#### Service Tests (1 file)
```
service/compiler_service_spec.spl
```

#### SDN Tests (5 files)
```
unit/sdn/document_spec.spl
unit/sdn/lexer_spec.spl
unit/sdn/parser_spec.spl
unit/sdn/compatibility_spec.spl
unit/sdn/roundtrip_spec.spl
unit/sdn/value_spec.spl
```

#### Other Tests (8 files)
```
unit/cli_spec.spl
unit/host/datetime_spec.spl
unit/dap/breakpoints_spec.spl
unit/dap/protocol_spec.spl
unit/dap/server_spec.spl
unit/game_engine/component_spec.spl
unit/game_engine/effects_spec.spl
fixtures/fixture_spec.spl
```

### Legend
- ✅ All modes (default)
- ⚠️ Mode-specific configuration needed
- ❌ Interpreter-only (reflection/parsing)

## Testing Strategy

### Unit Tests (Rust)
**Location:** `src/*/tests/`

1. Mode configuration parsing
2. Configuration hierarchy resolution
3. Mode set operations (union, intersection, difference)
4. Failure strategy logic
5. Mode availability detection

### System Tests (Simple)
**Location:** `simple/std_lib/test/system/spec/`

1. Multi-mode execution scenarios
2. Configuration inheritance validation
3. Skip behavior verification
4. Failure handling strategies
5. Reporting output format

### Integration Tests
**Location:** `simple/std_lib/test/integration/`

1. End-to-end mode switching
2. Cross-mode result consistency
3. Performance comparison accuracy
4. Config file discovery and loading

## Success Criteria

1. ✅ All 4 execution modes supported (interpreter, JIT, SMF×2)
2. ✅ Configuration works at all 5 levels (project → test)
3. ✅ Skip logic prevents unnecessary execution
4. ✅ Failure strategies implemented and tested
5. ✅ Clear mode-aware reporting
6. ✅ Performance overhead < 5% per mode
7. ✅ Zero breaking changes to existing tests
8. ✅ All ~100 spec tests pass in all applicable modes

## Open Questions

1. **JIT Implementation Status**
   - Is JIT mode fully functional?
   - What features are not yet compilable?
   - How to detect JIT compilation failures?

2. **LLVM Backend Timeline**
   - When will LLVM backend be available?
   - Should we skip LLVM mode by default initially?

3. **Mode Isolation**
   - Do modes share state or run in separate processes?
   - How to handle global state between modes?

4. **Performance Baseline**
   - What's acceptable overhead for multi-mode execution?
   - Should we parallelize mode execution?

5. **Backward Compatibility**
   - Can existing tests run without changes?
   - Default to all modes or interpreter-only?

## Next Steps

1. **Immediate:**
   - Define `ExecutionMode` enum
   - Prototype mode switching in spec runner
   - Test with arithmetic_spec.spl

2. **Week 1:**
   - Implement Phase 1 (Core Infrastructure)
   - Start Phase 2 (Configuration System)

3. **Week 2:**
   - Complete Phase 2
   - Start Phase 3 (Execution Engine)

4. **Week 3:**
   - Complete Phase 3
   - Implement Phase 4 (Skip & Failure Handling)

5. **Week 4:**
   - Implement Phase 5 (Reporting)
   - Rollout to all test files
   - Documentation and examples

## References

- [Feature Documentation](../features/feature.md#multi-mode-spec-test-execution-2050-2054)
- [Spec Framework](../../simple/std_lib/src/spec/README.md)
- [Test Documentation](../test.md)
- [Codegen Status](../codegen_status.md)
