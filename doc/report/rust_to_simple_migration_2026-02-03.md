# Rust to Simple Migration Status - February 2026

## Migration Philosophy

**Goal:** Self-hosting - maximize Simple code, minimize Rust code
**Strategy:** Keep only critical performance-sensitive code in Rust

---

## Current Status Overview

### ✅ Already Migrated to Simple

| Component | Lines | Status | Location |
|-----------|-------|--------|----------|
| **CLI** | ~500 | ✅ Complete | `src/app/cli/main.spl` |
| **Build System** | ~4,440 | ✅ Complete | `src/app/build/` |
| **Formatter** | ~698 | ✅ Complete | `src/app/formatter/main.spl` |
| **Linter** | ~500 | ✅ Complete | `src/app/lint/main.spl` |
| **LSP** | ~1,500 | ✅ Complete | `src/app/lsp/` |
| **DAP** | ~800 | ✅ Complete | `src/app/dap/` |
| **REPL** | ~400 | ✅ Complete | `src/app/repl/main.spl` |
| **Test Runner** | ~800 | ✅ Complete | `src/app/build/test.spl` |
| **Package Manager** | ~600 | ✅ Complete | `src/app/build/package.spl` |
| **Coverage CLI** | ~200 | ✅ Wrapper | `src/app/coverage/main.spl` |
| **Context Pack** | ~300 | ✅ Complete | `src/app/context/main.spl` |
| **Dep Graph** | ~250 | ✅ Complete | `src/app/depgraph/main.spl` |
| **MCP Server** | ~400 | ✅ Complete | `src/app/mcp/main.spl` |
| **Verification** | ~600 | ✅ Complete | `src/app/verify/main.spl` |
| **SSpec DocGen** | ~350 | ✅ Complete | `src/app/sspec_docgen/main.spl` |

**Total migrated:** ~12,000+ lines of application code

### 🔧 Partially Migrated (Simple wrapper, Rust impl)

| Component | Simple Wrapper | Rust Implementation | Migration Priority |
|-----------|----------------|---------------------|-------------------|
| Coverage Tools | `src/app/coverage/main.spl` | `rust/util/simple_mock_helper/` | Medium |
| Compiler | `src/compiler/` | `rust/compiler/` | Low (keep in Rust) |

### ⏸️ Keep in Rust (Critical Performance)

| Component | Lines | Reason | Location |
|-----------|-------|--------|----------|
| **Runtime** | ~15,000 | Performance critical | `rust/runtime/` |
| **Compiler Core** | ~45,000 | Bootstrap, performance | `rust/compiler/` |
| **Parser** | ~8,000 | Bootstrap parser | `rust/parser/` |
| **Driver** | ~2,000 | Binary entry point | `rust/driver/` |
| **GC** | ~3,000 | Performance critical | `rust/runtime/src/gc/` |
| **FFI Bridge** | ~1,500 | Runtime bridge | `rust/runtime/src/ffi/` |

**Total kept in Rust:** ~75,000 lines (core infrastructure)

### 🎯 Migration Candidates (Non-Critical)

| Component | Lines | Complexity | Priority | Notes |
|-----------|-------|------------|----------|-------|
| Coverage Generator | ~3,500 | Medium | **High** | Already has Simple wrapper |
| Mock Helper | ~3,500 | Medium | Medium | Testing utility |
| Arch Test | ~500 | Low | **High** | Simple utility |
| Test Utilities | ~5,000 | Low-Med | Medium | Helper functions |
| Doc Generator (old) | ~1,000 | Low | Low | May be obsolete |

**Total migration candidates:** ~13,500 lines

---

## Detailed Analysis

### High Priority: Arch Test Utility

**Location:** `rust/util/arch_test/`
**Size:** ~500 lines
**Purpose:** Test architecture detection
**Complexity:** Low
**Dependencies:** Minimal

**Migration Plan:**
1. Create `src/app/arch_test/main.spl`
2. Implement architecture detection in Simple
3. Use FFI only for OS-specific calls
4. Remove Rust version after verification

**Estimated effort:** 2-3 hours

---

### High Priority: Coverage Generator

**Location:** `rust/util/simple_mock_helper/src/bin/coverage_gen.rs`
**Size:** ~198 lines (CLI) + ~1,036 lines (coverage_extended.rs)
**Purpose:** Generate extended coverage reports from LLVM data
**Complexity:** Medium (JSON parsing, file I/O, data analysis)

**Already exists:**
- ✅ Simple wrapper: `src/app/coverage/main.spl` (200 lines)
- ❌ Implementation: Still in Rust via FFI

**Migration Plan:**
1. Implement JSON parsing in Simple (use `std.json` when available)
2. Implement YAML parsing in Simple (use `std.sdn` for now)
3. Port coverage analysis logic to Simple
4. Replace FFI calls with native Simple implementation
5. Remove Rust implementation

**Blockers:**
- Need JSON library in Simple (or SDN alternative)
- Need file I/O in Simple std library

**Estimated effort:** 8-10 hours

---

### Medium Priority: Mock Helper Core

**Location:** `rust/util/simple_mock_helper/src/`
**Size:** ~3,514 lines total
**Purpose:** Testing mocks and utilities
**Complexity:** Medium-High

**Components:**
- `api_scanner.rs` (391 lines) - Scan source for public API
- `coverage.rs` (571 lines) - Coverage analysis
- `ffi.rs` (534 lines) - FFI helpers
- `fluent.rs` (729 lines) - Fluent test API
- `mock_policy.rs` (290 lines) - Mock policies
- `test_check.rs` (421 lines) - Test verification

**Migration Strategy:**
- Phase 1: Migrate CLI tools (coverage_gen, smh_coverage)
- Phase 2: Migrate API scanner
- Phase 3: Migrate coverage analysis
- Phase 4: Keep FFI helpers in Rust (needed for runtime)

**Estimated effort:** 20-25 hours

---

### Low Priority: Obsolete Code Removal

**Candidates for removal:**

1. **Deprecated Test Files**
   - Check for tests migrated to SSpec
   - Remove duplicated Rust tests

2. **Old Build Scripts**
   - Build system now in Simple
   - Check for unused Makefile targets
   - Remove obsolete cargo build scripts

3. **Unused Utilities**
   - Check for utilities replaced by Simple versions
   - Remove dead code branches

**Investigation needed:** Scan codebase for:
- `#[deprecated]` annotations
- `TODO: remove` comments
- Files not referenced in Cargo.toml
- Unused imports

---

## Migration Roadmap

### Phase 1: Quick Wins (Week 1)
- ✅ Create migration status document (this file)
- ⏳ Migrate arch_test utility (2-3 hours)
- ⏳ Remove obsolete test files (3-4 hours)
- ⏳ Document FFI boundaries clearly (2 hours)

**Deliverable:** ~500 lines migrated, ~2,000 lines removed

### Phase 2: Coverage Tools (Week 2-3)
- ⏳ Implement JSON/YAML parsing in Simple
- ⏳ Migrate coverage_gen CLI logic
- ⏳ Migrate coverage analysis algorithms
- ⏳ Replace FFI calls with Simple implementation
- ⏳ Remove Rust coverage_gen

**Deliverable:** ~1,200 lines migrated, coverage tools 100% Simple

### Phase 3: Mock Helper (Week 4-5)
- ⏳ Migrate API scanner to Simple
- ⏳ Migrate test utilities to Simple
- ⏳ Keep only essential FFI helpers in Rust
- ⏳ Update documentation

**Deliverable:** ~2,500 lines migrated

### Phase 4: Polish & Optimize (Week 6)
- ⏳ Performance testing of migrated code
- ⏳ Optimize hot paths if needed
- ⏳ Update build system to remove Rust dependencies
- ⏳ Final cleanup and documentation

**Deliverable:** Migration complete, ~4,000+ lines migrated total

---

## Code Metrics

### Current Distribution

```
Rust Code:
  Runtime:     ~15,000 lines (keep)
  Compiler:    ~45,000 lines (keep)
  Parser:      ~8,000 lines (keep)
  Driver:      ~2,000 lines (keep)
  Tests:       ~35,000 lines (review for migration)
  Utilities:   ~3,500 lines (MIGRATE)
  Total:       ~108,500 lines

Simple Code:
  Compiler:    ~15,000 lines (high-level logic)
  Apps:        ~12,000 lines (tools, CLI, build)
  Std Lib:     ~8,000 lines (standard library)
  Tests:       ~5,000 lines (SSpec tests)
  Total:       ~40,000 lines

Ratio: 73% Rust, 27% Simple (application layer is ~50% Simple)
```

### Target Distribution (After Migration)

```
Rust Code:
  Runtime:     ~15,000 lines (keep)
  Compiler:    ~45,000 lines (keep)
  Parser:      ~8,000 lines (keep)
  Driver:      ~2,000 lines (keep)
  Core Tests:  ~20,000 lines (keep essential)
  Total:       ~90,000 lines (-18,500)

Simple Code:
  Compiler:    ~15,000 lines
  Apps:        ~16,000 lines (+4,000 migrated)
  Std Lib:     ~10,000 lines (+2,000 enhanced)
  Tests:       ~15,000 lines (+10,000 SSpec)
  Total:       ~56,000 lines (+16,000)

Ratio: 62% Rust, 38% Simple (application layer is ~80% Simple)
```

---

## Migration Guidelines

### When to Migrate to Simple

✅ **Do migrate:**
- CLI tools and user-facing applications
- Build scripts and development tools
- Test utilities and test generators
- Documentation generators
- Code analysis tools (non-performance critical)
- Configuration and orchestration
- Developer productivity tools

❌ **Don't migrate:**
- Runtime core (GC, memory management)
- Compiler performance-critical paths
- Low-level FFI bridge
- Bootstrap parser
- Performance-critical algorithms
- System-level operations requiring unsafe code

### Migration Checklist

For each component:
1. ✅ Identify all dependencies
2. ✅ Check if dependencies are available in Simple
3. ✅ Estimate complexity (Low/Medium/High)
4. ✅ Create Simple implementation
5. ✅ Add tests (SSpec if possible)
6. ✅ Verify functionality matches
7. ✅ Performance test if relevant
8. ✅ Update documentation
9. ✅ Remove Rust code
10. ✅ Update build system

---

## FFI Boundary Documentation

### Current FFI Usage

**Simple → Rust FFI:**
- File I/O: `rt_file_read`, `rt_file_write`, `rt_file_exists`
- Process: `sys_get_args`, `sys_exit`
- Coverage: `coverage_*` functions (to be migrated)
- Runtime: `rt_*` functions (keep)

**Rust → Simple:**
- Interpreter calls
- Plugin system
- Test execution

### Target FFI Boundary

After migration, FFI should only be:
1. **Runtime operations** - GC, memory, execution
2. **System calls** - OS-level operations
3. **Performance critical** - Hot path algorithms

All application logic should be in Simple.

---

## Benefits of Migration

### For Development
- ✅ Dogfooding - Using Simple to build Simple
- ✅ Faster iteration - No Rust compilation wait
- ✅ Easier contribution - More developers know Simple
- ✅ Better testing - Use SSpec for everything

### For Users
- ✅ Smaller binary - Less Rust code to compile
- ✅ More customizable - Users can modify Simple tools
- ✅ Better examples - Tools show idiomatic Simple
- ✅ Clearer architecture - Separation of concerns

### For Project
- ✅ Self-hosting milestone - Simple compiler in Simple
- ✅ Confidence in language - Production-ready
- ✅ Better documentation - Simple code as examples
- ✅ Reduced maintenance - One language to maintain

---

## Action Items

### Immediate (This Week)
1. ⏳ Migrate `rust/util/arch_test/` to Simple
2. ⏳ Audit test files for obsolete Rust tests
3. ⏳ Document current FFI boundary
4. ⏳ Create task list for coverage tool migration

### Short Term (Next 2 Weeks)
1. ⏳ Implement JSON parsing in Simple std lib
2. ⏳ Migrate coverage_gen to Simple
3. ⏳ Remove obsolete Rust test utilities
4. ⏳ Update build system dependencies

### Long Term (Next Month)
1. ⏳ Complete mock helper migration
2. ⏳ Achieve 80% Simple application layer
3. ⏳ Document migration patterns
4. ⏳ Update contributor guide

---

## Success Metrics

### Quantitative
- **Code ratio:** Target 40% Simple, 60% Rust (from 27%/73%)
- **Application layer:** Target 80% Simple (from 50%)
- **Lines migrated:** Target 4,000+ lines
- **Lines removed:** Target 2,000+ obsolete lines

### Qualitative
- ✅ All CLI tools in Simple
- ✅ All build system in Simple
- ✅ All developer tools in Simple
- ✅ Only core runtime in Rust
- ✅ Clear FFI boundary

---

## References

- Build system implementation: `src/app/build/`
- CLI implementation: `src/app/cli/main.spl`
- FFI specifications: `doc/spec/rust_to_simple_ffi.md`
- Coverage wrapper: `src/app/coverage/main.spl`
- Migration reports: `doc/report/arg_parsing_migration_2026-01-20.md`

---

**Status:** Migration ongoing - 27% Simple application code, target 40% overall
**Next milestone:** Migrate arch_test and coverage_gen (Week 1)
**End goal:** Self-hosting Simple compiler with minimal Rust core
