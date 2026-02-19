# API Surface Reduction Plan - Module Boundary Control

**Status:** Research Complete - Ready for Implementation
**Created:** 2026-02-11
**Goal:** Reduce exposed API surface by adding `__init__.spl` files to control module boundaries

---

## Executive Summary

**Current State:** Only 37 out of 273 directories (13.6%) have `__init__.spl` files
**Problem:** Uncontrolled API exposure, no module boundaries, difficult maintenance
**Solution:** Systematic addition of `__init__.spl` files with explicit exports
**Impact:** Better encapsulation, clearer APIs, easier refactoring, reduced coupling

---

## Strategy & Design Principles

### 1. **Explicit Over Implicit**
- Use `pub use` with specific type lists (not `.*` wildcards)
- Document what each module provides
- Make internal vs. public distinction clear

### 2. **Minimal Public API**
- Only export types/functions actually used by other modules
- Keep implementation details private
- Use `pub mod` only for submodules that need external access

### 3. **Layered Architecture**
```
Top-level __init__.spl (src/compiler_core_legacy/)
    └─> Sub-module __init__.spl (src/compiler_core_legacy/compiler/)
        └─> Leaf files (src/compiler_core_legacy/compiler/driver.spl)
```

### 4. **Documentation Standards**
Every `__init__.spl` must include:
- Module purpose (1-2 sentences)
- Public API exports (explicit list)
- Internal modules (marked as internal)
- Usage examples (for complex APIs)

---

## Implementation Phases

### Phase 1: Critical Foundation (3 Top-Level Modules)
**Priority:** CRITICAL
**Estimated Files:** 3
**Estimated Time:** 1 session

#### 1.1 Create `src/compiler_core_legacy/__init__.spl`
**Purpose:** Core language types (AST, tokens, lexer, parser)

**Exports to determine:**
- Review current usage: `grep -r "use core\." src/`
- Identify: Which types are imported externally?
- Likely exports: `Token`, `TokenType`, `AstNode`, `Type`, `parse`, `lex`

**Sub-modules:**
- `pub mod lexer` - public (used by compiler)
- `pub mod parser` - public (used by compiler)
- `pub mod ast` - public (used everywhere)
- `pub mod tokens` - public (used by lexer/parser consumers)
- `pub mod types` - public (used by type checker)
- `mod interpreter` - internal (only for REPL)
- `mod compiler` - internal (wrapped by compiler_core_legacy)
- `mod hir` - internal
- `mod mir` - internal
- `mod wffi` - internal

**Template:**
```simple
# Module: core
# Purpose: Core Simple language types and parsers
# Status: Public API - used by compiler and tools

# Public modules
pub mod lexer
pub mod parser
pub mod ast
pub mod tokens
pub mod types

# Internal modules
mod interpreter
mod compiler
mod hir
mod mir
mod wffi

# Re-export key types
pub use .lexer.{Lexer, LexResult, LexError}
pub use .parser.{Parser, ParseResult, ParseError}
pub use .ast.{AstNode, Expr, Stmt, Pattern, TypeExpr}
pub use .tokens.{Token, TokenType}
pub use .types.{Type, TypeContext}
```

#### 1.2 Create `src/lib/__init__.spl`
**Purpose:** Shared libraries (database, collections, execution)

**Exports to determine:**
- Review: `grep -r "use lib\." src/`
- Likely: Database types, pure functions, collection utilities

**Sub-modules:**
- `pub mod database` - public (BugDB, TestDB, FeatureDB)
- `pub mod pure` - public (28 utility functions)
- `pub mod collections` - public (advanced data structures)
- `mod execution` - internal (runtime helpers)
- `mod parser` - internal (library-specific parsing)
- `mod cuda` - internal (GPU runtime)
- `mod torch` - internal (ML runtime)
- `mod qemu` - internal (VM testing)
- `mod hooks` - internal
- `mod json` - internal
- `mod memory` - internal

**Template:**
```simple
# Module: lib
# Purpose: Shared libraries for compiler and tools
# Status: Public API - stable interfaces

# Public modules
pub mod database
pub mod pure
pub mod collections

# Internal modules
mod execution
mod parser
mod cuda
mod torch
mod qemu
mod hooks
mod json
mod memory

# Re-export common types
pub use .database.{BugDB, TestDB, FeatureDB, Query}
pub use .pure.*  # Pure functions are all public
pub use .collections.{LazySeq, PersistentDict, PersistentVec}
```

#### 1.3 Create `src/std/__init__.spl`
**Purpose:** Standard library modules

**Exports to determine:**
- This is the top-level stdlib - should re-export most submodules
- Review: What do users import from std?
- Likely: Most modules public, some internal (test, failsafe)

**Sub-modules:**
- `pub mod spec` - public (testing framework)
- `pub mod async` - public (async runtime)
- `pub mod concurrent` - public (concurrency primitives)
- `pub mod net` - public (networking)
- `pub mod compute` - public (computation)
- `pub mod gpu` - public (GPU operations)
- `pub mod sdn` - public (SDN format)
- `pub mod report` - public (diagnostics)
- `pub mod common` - public (shared utilities)
- `pub mod type` - public (type utilities)
- `mod test` - internal (testing internals)
- `mod failsafe` - internal (failure handling internals)
- `mod dependency_tracker` - internal

**Template:**
```simple
# Module: std
# Purpose: Simple standard library
# Status: Public API - language standard library

# Public modules (standard library interface)
pub mod spec
pub mod async
pub mod async_host
pub mod concurrent
pub mod net
pub mod compute
pub mod gpu
pub mod sdn
pub mod report
pub mod common
pub mod type

# Internal modules (implementation details)
mod test
mod failsafe
mod dependency_tracker
mod mcp

# Re-export commonly used functions
pub use .spec.{describe, it, expect, before, after}
pub use .async.{async_fn, await_result, spawn_task}
pub use .concurrent.{Mutex, RwLock, Semaphore}
```

---

### Phase 2: Major Application Modules (7 modules)
**Priority:** HIGH
**Estimated Files:** 7
**Estimated Time:** 2 sessions

#### 2.1 `src/app/build/__init__.spl` (26 files)
**Purpose:** Build system orchestration

**Current problem:** 26 files all exposed, no clear entry point

**Analysis needed:**
- Entry point: `main.spl` - likely public interface
- Internal: bootstrap, cargo, config, coverage, incremental, package
- Find: `grep -r "use app\.build\." src/`

**Proposed structure:**
```simple
# Module: app.build
# Purpose: Build system for Simple compiler
# Public API: build_project, BuildConfig

pub use .main.{build_project, BuildOptions}
pub use .types.{BuildResult, BuildProfile, BuildMode}

# Internal implementation
mod bootstrap
mod cargo
mod config
mod coverage
mod incremental
mod package
mod orchestrator
mod native
```

#### 2.2 `src/app/io/__init__.spl` (35 files)
**Purpose:** I/O abstraction layer (SFFI wrappers)

**Current problem:** 35 FFI wrappers all directly exposed

**Proposed structure:**
```simple
# Module: app.io
# Purpose: Unified I/O interface for Simple runtime
# Groups: fs, net, audio, compression, shell

# File I/O
pub use .file.{file_read, file_write, file_append, file_exists}
pub use .fs.{list_dir, create_dir, remove_dir, copy_file}

# Network I/O
pub use .http.{http_get, http_post, HttpRequest, HttpResponse}
pub use .tcp.{TcpStream, TcpListener}

# System I/O
pub use .shell.{shell_exec, shell_pipe, ShellResult}
pub use .process.{Process, spawn_process, wait_for_exit}

# Audio (specialized)
pub mod audio

# Internal FFI implementations
mod ffi_file
mod ffi_net
mod ffi_audio
mod ffi_compress
```

#### 2.3 `src/app/test_runner_new/__init__.spl` (24 files)
**Purpose:** Test execution framework

**Proposed structure:**
```simple
# Module: app.test_runner_new
# Purpose: Test discovery and execution
# Public API: run_tests, TestRunner

pub use .test_runner_main.{run_tests, TestConfig}
pub use .test_runner_execute.{TestRunner, TestResult}
pub use .test_runner_coverage.{CoverageCollector, CoverageReport}

# Internal modules
mod discovery
mod matcher
mod hooks
mod isolation
```

#### 2.4 `src/app/package/__init__.spl` (19 files)
**Purpose:** Package management

**Proposed structure:**
```simple
# Module: app.package
# Purpose: Package registry and dependency resolution
# Public API: resolve_deps, fetch_package

pub use .resolver.{resolve_dependencies, DependencyGraph}
pub use .registry.{PackageRegistry, fetch_package, publish_package}
pub use .types.{Package, PackageVersion, Dependency}

# Sub-modules
pub mod registry  # Will have its own __init__.spl

# Internal modules
mod cache
mod download
mod verify
```

#### 2.5 `src/app/ffi_gen/__init__.spl` (18 files)
**Purpose:** FFI wrapper code generation

**Proposed structure:**
```simple
# Module: app.ffi_gen
# Purpose: Generate Simple FFI wrappers from C/C++ headers
# Public API: generate_ffi_wrapper

pub use .main.{generate_ffi_wrapper, FfiGenConfig}
pub use .types.{FfiFunction, FfiType, FfiBinding}

# Internal generator components
mod parser
mod analyzer
mod codegen
mod template
```

#### 2.6 `src/app/wrapper_gen/__init__.spl` (11 files)
**Purpose:** Generic wrapper generation

#### 2.7 `src/app/duplicate_check/__init__.spl` (12 files)
**Purpose:** Code duplication detection

---

### Phase 3: Compiler Core Infrastructure (13 modules)
**Priority:** HIGH
**Estimated Files:** 13 main + 4 sub-modules
**Estimated Time:** 3-4 sessions

#### 3.1 `src/compiler_core_legacy/backend/__init__.spl` (38 files)
**Current problem:** Largest uncontrolled module - 38 codegen files

**Proposed structure:**
```simple
# Module: compiler_core_legacy.backend
# Purpose: Code generation backends for multiple targets
# Public API: CodegenBackend trait + factory

pub use .backend_api.{CodegenBackend, BackendFactory}
pub use .backend_types.{BackendTarget, CodegenOptions}

# Public backend implementations
pub mod llvm_backend
pub mod cuda_backend
pub mod wasm_backend
pub mod vulkan_backend

# Shared utilities (internal)
mod common
mod native

# Internal modules
mod capability_tracker
mod optimization_passes
mod type_mapper
```

**Sub-modules needed:**
- `backend/common/__init__.spl` (4 files)
- `backend/native/__init__.spl` (10 files)
- `backend/cuda/__init__.spl` (2 files)
- `backend/vulkan/__init__.spl` (2 files)

#### 3.2 `src/compiler_core_legacy/linker/__init__.spl` (20 files)
**Purpose:** Object file linking and SMF format

**Proposed structure:**
```simple
# Module: compiler_core_legacy.linker
# Purpose: Link compiled objects into executables
# Public API: link_objects, SMF format

pub use .link.{link_objects, LinkOptions, LinkResult}
pub use .smf_reader.{read_smf, SmfModule}
pub use .smf_writer.{write_smf, SmfBuilder}

# Internal implementation
mod linker_context
mod linker_wrapper
mod symbol_analysis
mod lib_smf
mod mold
```

#### 3.3 `src/compiler_core_legacy/monomorphize/__init__.spl` (19 files)
**Purpose:** Generic type instantiation

**Proposed structure:**
```simple
# Module: compiler_core_legacy.monomorphize
# Purpose: Instantiate generic types and functions
# Public API: monomorphize_module

pub use .engine.{monomorphize_module, MonoEngine}
pub use .types.{MonoInstance, InstantiationKey}

# Internal components
mod analyzer
mod rewriter
mod cache
mod tracker
mod table
mod cycle_detector
```

#### 3.4 `src/compiler_core_legacy/blocks/__init__.spl` (22 files)
**Purpose:** Block system (macros/DSL)

#### 3.5 `src/compiler_core_legacy/loader/__init__.spl` (8 files)
**Purpose:** Module loading and JIT

#### 3.6 `src/compiler_core_legacy/mir_opt/__init__.spl` (7 files)
**Purpose:** MIR optimizations

#### 3.7 `src/compiler_core_legacy/hir_lowering/__init__.spl` (6 files)
**Purpose:** AST → HIR lowering

#### 3.8 `src/compiler_core_legacy/parser/__init__.spl` (5 files)
**Purpose:** Parser infrastructure

#### 3.9 `src/compiler_core_legacy/type_infer/__init__.spl` (5 files)
**Purpose:** Type inference helpers

#### 3.10-3.13 Smaller modules (baremetal, borrow_check, desugar, etc.)

---

### Phase 4: Standard Library Modules (10 modules)
**Priority:** MEDIUM
**Estimated Files:** 10
**Estimated Time:** 2-3 sessions

#### 4.1 `src/std/async/__init__.spl` (10 files)
#### 4.2 `src/std/async_host/__init__.spl` (9 files)
#### 4.3 `src/std/concurrent/__init__.spl` (7 files)
#### 4.4 `src/std/spec/__init__.spl` (5 files)
#### 4.5 `src/std/compute/__init__.spl` (5 files)
#### 4.6 `src/std/net/__init__.spl` (4 files)
#### 4.7 `src/std/gpu/__init__.spl` (4 files)
#### 4.8-4.10 Smaller std modules

---

### Phase 5: Remaining Modules (100+ directories)
**Priority:** LOW
**Estimated Files:** 100+
**Estimated Time:** Ongoing

- All single-file modules in `app/` (can be batch-processed)
- Test support modules
- Internal utilities
- Remaining compiler_core_legacy modules

---

## Templates

### Template 1: Simple Module (Single Entry Point)
```simple
# Module: app.modulename
# Purpose: <1-2 sentence description>
# Public API: <main exported function/type>

# Re-export main interface
pub use .main.{main_function, MainType}

# Internal implementation
mod helper1
mod helper2
mod types
```

### Template 2: Multi-Facet Module (Multiple Sub-APIs)
```simple
# Module: app.modulename
# Purpose: <description>
# Groups: <list logical groups>

# Group 1: <Description>
pub use .api1.{Type1, func1}

# Group 2: <Description>
pub use .api2.{Type2, func2}

# Public sub-modules
pub mod submodule1
pub mod submodule2

# Internal implementation
mod internal1
mod internal2
```

### Template 3: Pure Re-export Module
```simple
# Module: lib.pure
# Purpose: Pure utility functions (no side effects)
# Status: All functions public

# All pure functions are part of public API
pub use .array.*
pub use .string.*
pub use .math.*
pub use .functional.*
```

---

## Analysis Methodology

For each module requiring `__init__.spl`:

### Step 1: Identify External Usage
```bash
# Find all imports of this module from outside
grep -r "use app\.build\." src/ | grep -v "src/app/build"
```

### Step 2: Categorize Files
- **Entry points:** Files that provide main API (often `main.spl`, `api.spl`)
- **Types:** Shared types (often `types.spl`, `data.spl`)
- **Helpers:** Internal utilities (should be private)
- **Tests:** Test-only code (mark internal)

### Step 3: Design Export List
- Start minimal: Only export what's currently used
- Group related exports
- Document rationale for each export

### Step 4: Validate
```bash
# Compile after adding __init__.spl
bin/simple build

# Run tests
bin/simple test
```

---

## Validation & Testing

### Test Plan
1. **Compilation test:** `bin/simple build` must succeed
2. **Test suite:** `bin/simple test` must pass (all 409 tests)
3. **External imports:** Verify existing imports still work
4. **No breakage:** No change in user-facing behavior

### Regression Detection
- Before starting Phase N: Record test baseline
- After completing Phase N: Compare test results
- Any test failures = revert and fix

### Progressive Rollout
- Do NOT add all __init__.spl files at once
- Complete each phase fully before moving to next
- Validate after each phase
- Commit after each phase with descriptive message

---

## Expected Impact

### Positive Effects
1. **Clearer API boundaries** - Know what's public vs. internal
2. **Easier refactoring** - Internal changes don't break external code
3. **Better documentation** - __init__.spl acts as module documentation
4. **Reduced coupling** - Explicit imports make dependencies visible
5. **Faster compilation** - Compiler can skip internal modules when not needed
6. **IDE support** - Better autocomplete (only show public APIs)

### Potential Issues
1. **Import changes** - Some imports may need updating (minor)
2. **Circular deps** - May expose hidden circular dependencies
3. **Over-restriction** - May need to make some internal things public (iterate)

### Metrics to Track
- Number of modules with __init__.spl: 37 → 150+ (target 80% coverage)
- Average public API size per module: TBD → <10 exports (target)
- External import count: TBD → reduced by 50% (target)

---

## Implementation Checklist

### Phase 1 (Critical) - Session 1
- [ ] Create `src/compiler_core_legacy/__init__.spl`
  - [ ] Analyze external imports
  - [ ] Design export list
  - [ ] Write __init__.spl
  - [ ] Test compilation
- [ ] Create `src/lib/__init__.spl`
  - [ ] Analyze external imports
  - [ ] Design export list
  - [ ] Write __init__.spl
  - [ ] Test compilation
- [ ] Create `src/std/__init__.spl`
  - [ ] Analyze external imports
  - [ ] Design export list
  - [ ] Write __init__.spl
  - [ ] Test compilation
- [ ] Run full test suite
- [ ] Commit Phase 1 results

### Phase 2 (Major App Modules) - Sessions 2-3
- [ ] `src/app/build/__init__.spl`
- [ ] `src/app/io/__init__.spl`
- [ ] `src/app/test_runner_new/__init__.spl`
- [ ] `src/app/package/__init__.spl`
  - [ ] `src/app/package/registry/__init__.spl`
- [ ] `src/app/ffi_gen/__init__.spl`
- [ ] `src/app/wrapper_gen/__init__.spl`
- [ ] `src/app/duplicate_check/__init__.spl`
- [ ] Test and commit

### Phase 3 (Compiler Core) - Sessions 4-7
- [ ] `src/compiler_core_legacy/backend/__init__.spl`
  - [ ] Sub-modules: common, native, cuda, vulkan
- [ ] `src/compiler_core_legacy/linker/__init__.spl`
- [ ] `src/compiler_core_legacy/monomorphize/__init__.spl`
- [ ] `src/compiler_core_legacy/blocks/__init__.spl`
- [ ] `src/compiler_core_legacy/loader/__init__.spl`
- [ ] `src/compiler_core_legacy/mir_opt/__init__.spl`
- [ ] `src/compiler_core_legacy/hir_lowering/__init__.spl`
- [ ] `src/compiler_core_legacy/parser/__init__.spl`
- [ ] `src/compiler_core_legacy/type_infer/__init__.spl`
- [ ] 4 smaller modules
- [ ] Test and commit

### Phase 4 (Standard Library) - Sessions 8-10
- [ ] 10 std/ subdirectories
- [ ] Test and commit

### Phase 5 (Remaining) - Ongoing
- [ ] Batch process remaining modules
- [ ] Continuous improvement

---

## Success Criteria

### Phase 1 Complete
- ✓ 3 top-level modules have __init__.spl
- ✓ All tests pass
- ✓ No external API breakage
- ✓ Documentation updated

### Phase 2 Complete
- ✓ 7 major app modules controlled
- ✓ External imports reduced by 30%
- ✓ All tests pass

### Phase 3 Complete
- ✓ Compiler core has clean boundaries
- ✓ Backend/linker/monomorphize isolated
- ✓ All tests pass

### Final Success
- ✓ 80%+ coverage (220+ __init__.spl files)
- ✓ <10 average exports per module
- ✓ All documentation updated
- ✓ Zero test regressions

---

## Next Steps

**Immediate:** Start Phase 1
1. Read `.claude/agents/code.md` for implementation guidelines
2. Analyze `src/compiler_core_legacy/` external imports
3. Create first `__init__.spl` (core)
4. Iterate through Phase 1 checklist

**To begin:** Request approval to proceed with Phase 1 implementation
