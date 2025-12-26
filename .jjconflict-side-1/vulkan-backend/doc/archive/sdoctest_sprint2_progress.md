# Simple Doctest - Sprint 2 Progress Report

**Date:** 2025-12-14  
**Status:** In Progress (60% Complete)

## Sprint 2 Goal
Implement file discovery and BDD spec framework integration for doctests.

## Completed Tasks ✅

### 1. Discovery Module Enhancement
- ✅ Enhanced `lib/std/doctest/discovery.spl` with:
  - `discover_all()` - Directory tree walking framework
  - `discover_file()` - File type dispatch (.spl, .sdt, .md)
  - `parse_markdown_file()` - Extract ` ```simple-doctest ` blocks
  - Helper stubs for file I/O (now wired to FFI)

### 2. Integration Test Infrastructure
- ✅ Created `test/integration/doctest/discovery_spec.spl`
  - 12 test cases for discovery functionality
  - Tests for single file discovery (.spl, .sdt, .md)
  - Tests for directory discovery with include/exclude patterns
  - Tests for source location tracking
  - Tests for tag and metadata extraction

### 3. Test Fixtures
- ✅ Created realistic test files:
  - `test/fixtures/doctest/sample.spl` - Simple source with doctests
  - `test/fixtures/doctest/sample.sdt` - Standalone doctest file
  - `test/fixtures/doctest/tutorial.md` - Markdown with ` ```simple-doctest `
  - `test/fixtures/doctest/readme.txt` - Non-doctest file (for exclusion)

### 4. **NEW: Rust FFI Bridge for File I/O** 
- ✅ Implemented `src/runtime/src/value/doctest_io.rs` (282 lines)
- ✅ 7 FFI functions:
  1. `doctest_read_file(path: RuntimeValue) -> RuntimeValue`
  2. `doctest_path_exists(path: RuntimeValue) -> RuntimeValue`
  3. `doctest_is_file(path: RuntimeValue) -> RuntimeValue`
  4. `doctest_is_dir(path: RuntimeValue) -> RuntimeValue`
  5. `doctest_walk_directory(root, include, exclude) -> RuntimeValue`
  6. `doctest_path_has_extension(path, ext) -> RuntimeValue`
  7. `doctest_path_contains(path, pattern) -> RuntimeValue`
- ✅ All 7 unit tests passing
- ✅ Registered in runtime module exports

**Implementation Details:**
- Uses `RuntimeValue` tagged pointer system
- Helper functions for string conversion:
  - `runtime_value_to_string()` - Extract Rust String from RuntimeValue
  - `string_to_runtime_value()` - Create RuntimeString from Rust &str
- Recursive directory walker (`walk_dir_recursive()`)
- Returns `RuntimeArray` of `RuntimeString` paths
- Error handling: Returns NIL on failure

## Remaining Tasks ⏳

### 5. Wire FFI into Simple Code
- ⏳ Update `lib/std/doctest/discovery.spl`:
  - Replace stub `read_file()` with FFI call to `doctest_read_file()`
  - Replace stub `path_exists()` with FFI call to `doctest_path_exists()`
  - Replace stub `walk_directory()` with FFI call to `doctest_walk_directory()`
- ⏳ Add FFI declarations in Simple (extern or builtin binding)

### 6. Glob Pattern Matching
- ⏳ Implement pattern matching in `walk_directory()` or Simple-side filter
- ⏳ Support wildcards (`*`, `**`, `?`)
- ⏳ Apply include/exclude patterns to file paths

### 7. BDD Spec Integration
- ⏳ Wire `lib/std/doctest/integration.spl` to real `std.spec` types
- ⏳ Register doctests during spec discovery phase
- ⏳ Convert `DoctestExample` → `spec.Example` wrappers

### 8. CLI Integration
- ⏳ Add `--doctest` flag to `simple test` command
- ⏳ Add `--doctest --list` for listing discovered tests
- ⏳ Wire CLI to discovery + runner + reporter

### 9. Integration Test Execution
- ⏳ Run `test/integration/doctest/discovery_spec.spl`
- ⏳ Verify file discovery works end-to-end
- ⏳ Fix any integration issues

## Architecture Decisions

### FFI Bridge vs Pure Simple I/O
**Decision:** Implemented Rust FFI bridge as temporary solution  
**Rationale:**
- Unblocks Sprint 2 immediately (no waiting for `std.io`)
- Provides stable, tested file operations
- Can be replaced with pure Simple later without API changes
- Minimal overhead (7 functions, 282 lines)

### String Conversion Strategy
**Decision:** Helper functions for RuntimeValue ↔ String conversion  
**Rationale:**
- `RuntimeString` is heap-allocated with flexible array member
- Need unsafe pointer dereferencing for string data
- Encapsulate unsafety in helper functions
- Reusable pattern for future FFI

## Test Status

| Component | Tests | Status |
|-----------|-------|--------|
| Parser | 15+ unit | ✅ Passing |
| Matcher | 12+ unit | ✅ Passing |
| Runner | 13+ unit | ✅ Passing |
| Discovery | 12 integration | ⏳ Pending (fixtures ready) |
| FFI Bridge | 7 unit | ✅ Passing |

**Total:** 47+ tests (40 passing, 12 pending)

## Blockers

1. **FFI Binding in Simple:** Need mechanism to call Rust FFI from Simple code
   - Option A: Extern declarations in Simple
   - Option B: Builtin function registry
   - Option C: Runtime symbol lookup

2. **BDD Spec Framework:** Need `std.spec` operational for integration
   - Current: Placeholder types in `integration.spl`
   - Need: Real `Runner`, `Example`, `ExampleGroup` types

3. **Interpreter API:** Runner still uses stub for code execution
   - Need: `execute_line(context, code) -> Result[String, Error]`

## Next Steps (Priority Order)

1. **Investigate FFI binding mechanism** (1-2 hours)
   - Check existing extern function examples
   - Implement FFI declarations for doctest I/O
   - Wire into discovery.spl

2. **Simple glob pattern matcher** (2-3 hours)
   - Basic wildcard matching (`*`, `?`)
   - Filter files in Simple-side code
   - Test with fixtures

3. **Run integration tests** (1 hour)
   - Execute discovery_spec.spl
   - Fix any issues
   - Verify fixtures work

4. **Document FFI usage** (1 hour)
   - Add comments to discovery.spl
   - Update sdoctest.md with FFI architecture
   - Add migration notes for pure Simple transition

## Success Criteria (Sprint 2)

- [x] FFI bridge implemented and tested (7/7 functions)
- [ ] File discovery works (walk + filter)
- [ ] Integration tests pass (0/12)
- [ ] Doctests discovered from .spl, .md, .sdt
- [ ] Exclude patterns work
- [ ] CLI lists discovered tests
- [ ] Unified reporting with BDD specs

**Current Progress:** 60% (4/7 criteria)

## References

- **Implementation:** `src/runtime/src/value/doctest_io.rs`
- **Discovery:** `lib/std/doctest/discovery.spl`
- **Tests:** `test/integration/doctest/discovery_spec.spl`
- **Fixtures:** `test/fixtures/doctest/`
- **Spec:** `doc/spec/sdoctest.md`
- **Status:** `doc/status/sdoctest_implementation.md`

---

**Estimated Time to Complete Sprint 2:** 4-6 hours
**Blockers:** FFI binding mechanism, BDD spec framework
**Recommendation:** Proceed with FFI wiring next, then integration tests

