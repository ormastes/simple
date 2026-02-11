# Skipped Tests Analysis

**Date:** 2026-02-11
**Total Skipped Tests:** 606
**Test Files Affected:** 37

## Executive Summary

This analysis covers all skipped tests in the codebase and categorizes them by feature area. Each category represents a significant feature implementation effort.

## Major Feature Categories

### 1. Async/Await System (150+ tests)
**Files:**
- `test/feature/async_features_spec.spl` - 28 tests
- `test/feature/stackless_coroutines_spec.spl` - 4 tests
- `test/unit/std/async_spec.spl` - 9 tests
- `test/unit/std/async_embedded_spec.spl` - 22 tests
- `test/unit/std/async_host_spec.spl` - 47 tests

**Required Features:**
- `async fn` syntax and semantics
- `await` operator
- Future types and combinators
- Generator/yield syntax
- Actor model (spawn/send/receive)
- Coroutine runtime (embedded and host)
- Task scheduler with priorities
- JoinSet, FuturesUnordered collections
- Cancellation tokens

**Implementation Complexity:** VERY HIGH
- Requires runtime system changes
- New AST nodes and HIR/MIR lowering
- Async runtime integration
- State machine generation for async functions

---

### 2. GPU/CUDA Runtime (80+ tests)
**Files:**
- `test/unit/std/gpu_async_pipeline_spec.spl` - 43 tests
- `test/unit/std/gpu_context_spec.spl` - 23 tests
- `test/unit/std/gpu_runtime_spec.spl` - 14 tests

**Required Features:**
- GPU context management (CUDA backend)
- Device memory allocation/deallocation
- Async GPU operations (streams, events)
- Multi-batch pipelining (upload/compute/download overlap)
- Error handling and recovery
- Backend abstraction (CUDA, potentially others)

**Implementation Complexity:** VERY HIGH
- Requires CUDA FFI bindings
- Complex async coordination
- Hardware-dependent testing

---

### 3. Debugger Infrastructure (100+ tests)
**Files:**
- `test/unit/app/interpreter/debug_spec.spl` - 113 tests

**Required Features:**
- Breakpoint management (add/remove/toggle/list)
- Watch expressions
- Step over/into/out
- Call stack inspection
- Debug command parser
- Debug levels (Off/Error/Warn/Info/Debug/Trace)
- Source location mapping

**Implementation Complexity:** HIGH
- Requires interpreter instrumentation
- State management
- Expression evaluation in debug context

---

### 4. Baremetal/Embedded (50+ tests)
**Files:**
- `test/system/baremetal/arm32_boot_spec.spl` - 9 tests
- `test/system/baremetal/arm64_boot_spec.spl` - 6 tests
- `test/system/baremetal/riscv64_boot_spec.spl` - 5 tests
- `test/system/baremetal/x86_boot_spec.spl` - 8 tests
- `test/system/baremetal/x86_64_boot_spec.spl` - 6 tests
- `test/system/baremetal/hello_riscv32_semihost_spec.spl` - 4 skip() calls
- `test/system/baremetal/debug_boot_spec.spl` - 1 test

**Required Features:**
- Multiboot header generation (x86/x86_64)
- Exception vector tables (ARM32/ARM64/RISC-V64)
- Boot sequence implementation per architecture
- Stack setup and alignment
- Startup CRT for embedded targets
- QEMU integration testing

**Implementation Complexity:** VERY HIGH
- Architecture-specific assembly
- Linker script generation
- QEMU/hardware testing infrastructure

---

### 5. Compiler Bootstrapping (15+ tests)
**Files:**
- `test/feature/bootstrap_spec.spl` - 15 tests

**Required Features:**
- Full compiler self-hosting
- Lexer -> TreeSitter -> Parser -> HIR -> MIR -> Codegen pipeline
- Symbol table population
- MIR basic block generation
- Generation equivalence testing

**Implementation Complexity:** VERY HIGH
- Requires feature-complete compiler
- Multiple compiler stages need work

---

### 6. Generic Type System (30+ tests)
**Files:**
- `test/unit/compiler/generic_template_spec.spl` - 30 tests

**Required Features:**
- Generic function templates
- Generic struct templates
- Template metadata tracking
- Deferred monomorphization
- Specialization caching
- Type argument validation
- Nested generic types

**Implementation Complexity:** HIGH
- Type system extensions
- Monomorphization pass
- Cache management

---

### 7. Windows Platform Support (50+ tests)
**Files:**
- `test/system/platform/windows_spec.spl` - 48 tests
- `test/system/platform/cross_platform_spec.spl` - 2 tests

**Required Features:**
- Windows path handling (backslashes, UNC, MinGW)
- Windows command resolution (.exe extension)
- MSVC/lld-link detection
- Library name conversion (.a -> .lib)
- Visual Studio path detection
- cmd.exe process execution
- Path cache for performance

**Implementation Complexity:** MEDIUM-HIGH
- Platform-specific FFI
- Cross-platform testing infrastructure

---

### 8. Linker and Library Format (20+ tests)
**Files:**
- `src/compiler_core/linker/test/lib_smf_spec.spl` - 8 tests
- `src/compiler/linker/test/lib_smf_spec.spl` - 8 tests
- `test/unit/compiler/linker/lib_smf_spec.spl` - 8 tests

**Required Features:**
- SMF (Simple Module Format) library file operations
- Add/write/open/list modules
- Module existence checking
- Module data extraction
- Library composition

**Implementation Complexity:** MEDIUM
- Requires file I/O FFI
- Binary format specification

---

### 9. Test Database Features (20+ tests)
**Files:**
- `test/unit/app/tooling/test_db_concurrency_spec.spl` - 11 tests
- `test/unit/app/tooling/test_db_edge_cases_spec.spl` - 9 tests
- `test/unit/app/test_analysis_spec.spl` - 9 tests

**Required Features:**
- Concurrent write safety (file locking)
- Multiple reader support
- Lock timeout handling
- Stale lock detection
- Backup/restore on failure
- Unicode support
- Large database handling
- Test analysis and statistics

**Implementation Complexity:** MEDIUM
- Needs file locking FFI
- Process coordination

---

### 10. CLI Performance Benchmarking (15+ tests)
**Files:**
- `test/benchmark/cli_dispatch_perf_spec.spl` - 15 tests

**Required Features:**
- Rust FFI handler baseline
- Performance comparison infrastructure
- Slowdown factor calculation
- Millisecond-level timing
- Command dispatch timing

**Implementation Complexity:** MEDIUM
- Requires Rust FFI implementation
- Benchmark infrastructure

---

### 11. Parser Features (10+ tests)
**Files:**
- `test/feature/parser_dual_argument_syntax_spec.spl` - 7 tests
- `test/feature/parser_static_keyword_spec.spl` - 1 test (commented)

**Required Features:**
- No-paren function call syntax
- Colon vs equals argument syntax equivalence
- Whitespace handling edge cases
- Trait `implements` keyword
- Static methods in trait implementations

**Implementation Complexity:** MEDIUM
- Parser extensions
- AST modifications

---

### 12. Interpreter/Tooling (30+ tests)
**Files:**
- `test/unit/app/interpreter/symbol_spec.spl` - 4 tests
- `test/unit/app/tooling/arg_parsing_spec.spl` - 9 tests
- `test/integration/remote_riscv32_spec.spl` - 3 skip() calls
- `test/unit/lib/qemu_spec.spl` - 2 skip() calls

**Required Features:**
- Symbol interning system
- Argument parsing flags
- Remote QEMU execution
- GDB/QEMU tool detection

**Implementation Complexity:** LOW-MEDIUM

---

### 13. Math/Numeric Features (10+ tests)
**Files:**
- `test/feature/floor_division_fdiv_spec.spl` - 7 tests
- `test/feature/architecture_spec.spl` - 2 tests

**Required Features:**
- Division by zero error handling
- Float special cases (infinity, NaN)
- Math block floor division
- Architecture parsing (AVR, MSP430)

**Implementation Complexity:** LOW-MEDIUM

---

### 14. Compiler Block Testing (20+ tests)
**Files:**
- `test/unit/compiler/blocks/testing_spec.spl` - 18 tests

**Required Features:**
- Try/catch syntax support (blocker)
- Block testing helpers
- Mock blocks
- Validation assertions

**Implementation Complexity:** HIGH
- Requires exception handling system

---

### 15. Unified Execution Framework (15+ tests)
**Files:**
- `test/unit/lib/unified_execution_spec.spl` - 15 tests

**Required Features:**
- Execution adapters (local, GDB MI)
- Target configuration (QEMU RISC-V, x86_64)
- Test sessions with GDB
- Multi-test runner
- Transparent remote execution

**Implementation Complexity:** HIGH
- GDB MI protocol
- QEMU coordination

---

### 16. Misc Features (10+ tests)
**Files:**
- `test/unit/std/binary_io_spec.spl` - 1 test (reader.skip)
- Various other files

**Required Features:**
- Binary I/O skip operation
- Various small features

**Implementation Complexity:** LOW

---

## Blocked by Runtime Limitations

Many tests are blocked by current runtime limitations (see CLAUDE.md):

1. **Try/Catch/Throw** - Required for error handling tests
2. **Generics at Runtime** - Required for generic type tests
3. **Closure Capture Modification** - Required for some async tests
4. **Module Closures** - Required for some integration tests

---

## Implementation Strategy

### Phase 1: Foundation (Weeks 1-4)
- Fix runtime limitations (try/catch, generics)
- Implement file I/O FFI for library operations
- Add file locking FFI for test database concurrency

### Phase 2: Core Language Features (Weeks 5-12)
- Generic type system with monomorphization
- Parser extensions (dual argument syntax, trait implements)
- Symbol interning system

### Phase 3: Async System (Weeks 13-20)
- Async/await syntax and runtime
- Future types and combinators
- Task scheduler
- Generator/yield support

### Phase 4: Platform Support (Weeks 21-24)
- Windows platform support
- Cross-platform path handling
- MSVC/linker detection

### Phase 5: Advanced Features (Weeks 25-32)
- Debugger infrastructure
- GPU runtime (CUDA backend)
- Baremetal boot support

### Phase 6: Testing & Tooling (Weeks 33-36)
- Performance benchmarking
- Test database features
- Unified execution framework

### Phase 7: Bootstrapping (Weeks 37-40)
- Compiler self-hosting
- Full compilation pipeline
- Generation equivalence

---

## Estimated Total Effort

**Total Development Time:** 40+ weeks (9-10 months)
**Lines of Code:** 50,000+ LOC
**New FFI Bindings:** 30+ extern functions
**New Syntax:** async/await, yield, implements, dual argument syntax

This represents a fundamental expansion of the Simple language to production-level capabilities.

---

## Recommendations

1. **Prioritize by Dependencies:** Start with runtime fixes and FFI
2. **Incremental Implementation:** One feature category at a time
3. **Testing Strategy:** Implement feature -> unskip tests -> verify
4. **Documentation:** Update language spec as features are added
5. **Version Planning:** Consider this a major version bump (v2.0?)

---

## Next Steps

**Option A (Full Implementation):** Proceed with Phase 1 and implement all features over 9-10 months

**Option B (Prioritized Subset):** Select highest-value features:
- Generic type system (enables code reuse)
- Debugger infrastructure (improves developer experience)
- Windows support (expands platform reach)
- Async/await (enables modern patterns)

**Option C (Targeted Fixes):** Focus on unblocking specific use cases:
- Fix runtime limitations first
- Implement only features needed for current projects
- Leave advanced features (GPU, baremetal) as future work

---

## Conclusion

Implementing all 606 skipped tests requires building multiple major language features. This is feasible but represents a multi-month, multi-person effort. Recommend scoping discussions before proceeding.
