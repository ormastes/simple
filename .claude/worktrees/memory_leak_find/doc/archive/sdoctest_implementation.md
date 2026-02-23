# Simple Doctest (sdoctest) - Implementation Status

**Last Updated:** 2025-12-14

## Overview

Simple doctest is a Python doctest-inspired framework for embedding executable examples in documentation. It's being implemented in 4 sprints across the Simple standard library (`lib/std/doctest/`).

## Current Status: Sprint 2 (Discovery and Integration)

### Sprint 1: Core Parser and Runner ✅ COMPLETE

**Modules Implemented:**
- ✅ `parser.spl` - Extract `>>>` examples from strings
- ✅ `matcher.spl` - Exact, wildcard, and exception matching
- ✅ `runner.spl` - Execute examples in isolated interpreter

**Features:**
- ✅ Parse `>>>` prompt syntax
- ✅ Parse `...` continuation lines
- ✅ Parse expected output (exact strings)
- ✅ Parse expected exceptions (`Error: Type` or `Error: Type: message`)
- ✅ Wildcard matching (`.` for any char, `*` for any sequence)
- ✅ Setup/Teardown blocks per docstring
- ✅ Extract docstrings from `.spl` files (via `///` comment regex)
- ✅ Parse standalone `.sdt` files
- ✅ Timeout support (configurable per example)
- ✅ Tag support (for filtering)

**Tests:**
- ✅ 40+ unit tests written
  - `test/unit/doctest/parser_spec.spl` (166 lines)
  - `test/unit/doctest/matcher_spec.spl` (149 lines)
  - `test/unit/doctest/runner_spec.spl` (172 lines)

**Known Limitations:**
- ⚠️ Interpreter integration uses placeholder (needs real Simple REPL/interpreter API)
- ⚠️ File I/O uses stubs (needs `std.io` integration)

---

### Sprint 2: Discovery and Integration ⏳ IN PROGRESS (60% complete)

**Modules Enhanced:**
- ✅ `discovery.spl` - File walking and discovery framework
  - ✅ `discover_all()` - walk directory tree
  - ✅ `discover_file()` - dispatch by extension
  - ✅ `parse_markdown_file()` - extract ` ```simple-doctest ` blocks
  - ✅ Rust FFI bridge for file I/O (7 functions, 282 lines, 7 tests passing)
    - `src/runtime/src/value/doctest_io.rs`
    - `doctest_read_file`, `doctest_path_exists`, `doctest_is_file`
    - `doctest_is_dir`, `doctest_walk_directory`, `doctest_path_has_extension`
    - `doctest_path_contains`
  - ⏳ Wire FFI into Simple code
  - ⏳ Implement glob pattern matching

**Integration Tests:**
- ✅ Created `test/integration/doctest/discovery_spec.spl` (12 test cases)
- ✅ Created test fixtures:
  - `test/fixtures/doctest/sample.spl` - Simple source with doctests
  - `test/fixtures/doctest/sample.sdt` - Standalone doctest file
  - `test/fixtures/doctest/tutorial.md` - Markdown with doctests
  - `test/fixtures/doctest/readme.txt` - Non-doctest file
- ⏳ Run integration tests (pending FFI wiring)

**Remaining Tasks (Sprint 2):**
1. ⏳ Wire FFI functions into discovery.spl
2. ⏳ Implement glob pattern matching
3. ⏳ Hook into `spec.runner`
4. ⏳ CLI integration (`simple test --doctest`)
5. ⏳ Run and verify integration tests

**Blockers:**
- 🔒 **FFI Binding:** Need mechanism to call Rust FFI from Simple
- 🔒 **BDD Spec Framework:** Need `std.spec.Runner` for integration
- 🔒 **Interpreter:** Need stable REPL/interpreter API

---

### Sprint 3: Advanced Features 📋 PLANNED

**Features:**
- Tag filtering (`@doctest(tag: ...)` metadata)
- REPL recording mode (`simple repl --record output.sdt`)
- Configuration via `simple.toml`
- Multi-line string normalization
- Performance optimizations (parallel execution)

**Tests:**
- 15+ system tests for advanced features

---

### Sprint 4: Coverage and Polish 📋 PLANNED

**Features:**
- Coverage integration (doctests contribute to public function touch)
- Documentation examples (migrate existing docs)
- Migration guide for adopters
- CI integration (run doctests on every commit)

**Deliverables:**
- 100% of `lib/std` has doctest examples
- Complete developer guide
- Performance benchmarks

---

## Architecture

### Module Hierarchy

```
lib/std/doctest/
  __init__.spl        # Re-exports all modules
  parser.spl          # Parse >>> examples from strings ✅
  matcher.spl         # Match output (exact, wildcard, exception) ✅
  runner.spl          # Execute in isolated interpreter ✅
  discovery.spl       # Find doctests in files ⏳
  reporter.spl        # Format results 🔜
  integration.spl     # Hook into spec.runner 🔜
```

### Data Flow

```
Source Files (.spl, .md, .sdt)
       │
       ▼
   discovery.discover_all()
       │
       ▼
   List[DoctestExample]
       │
       ▼
   integration.create_example_groups()
       │
       ▼
   spec.runner (unified test execution)
       │
       ▼
   reporter.format_results()
       │
       ▼
   Console output / Coverage report
```

### Key Data Structures

```simple
struct DoctestExample:
    source: String              # File path
    location: SourceLocation    # File:line
    setup: List[String]         # >>> lines from Setup block
    code: List[String]          # >>> and ... lines
    expected: Expected          # Output or exception
    teardown: List[String]      # >>> lines from Teardown
    tags: Set[String]           # Metadata tags
    mode: String                # "inline" or "isolated"
    timeout_ms: Int             # Timeout in milliseconds

enum Expected:
    Output(String)              # Exact string match
    Exception(String, Option[String])  # (type, message)
    Empty                       # No output
```

---

## Test Coverage

| Module | Unit Tests | Integration Tests | System Tests |
|--------|------------|-------------------|--------------|
| parser.spl | ✅ 15+ | - | - |
| matcher.spl | ✅ 12+ | - | - |
| runner.spl | ✅ 13+ | - | - |
| discovery.spl | - | ⏳ 12 | - |
| integration.spl | - | 🔜 | 🔜 |
| reporter.spl | 🔜 | - | - |

**Total:** 40+ unit tests, 12 integration tests (pending), 0 system tests (planned)

---

## Dependencies

### Internal (Simple stdlib)
- 🔒 `std.io` - File system operations (read, walk, exists)
- 🔒 `std.spec` - BDD spec framework (Runner, Example, ExampleGroup)
- 🔒 `std.path` - Path manipulation and glob matching
- 🔒 `std.collections` - Set, Dict, List utilities

### External (Runtime)
- ⚠️ Simple interpreter/REPL API (for executing doctest code)
- ⚠️ CLI infrastructure (for `simple test --doctest` command)

---

## Next Steps (Immediate)

### Option A: Implement with Rust Bridge (Fast Path)
1. Create Rust bridge functions in `src/driver/src/`:
   - `doctest_read_file(path: &str) -> String`
   - `doctest_walk_dir(root: &str, patterns: &[&str]) -> Vec<String>`
   - `doctest_execute_code(code: &str) -> Result<String, String>`
2. Export to Simple FFI via runtime
3. Wire into discovery.spl
4. Run integration tests

### Option B: Wait for stdlib (Clean Path)
1. Complete `lib/std/io` module
2. Complete `lib/std/spec` framework
3. Wire together via pure Simple
4. Run integration tests

**Recommendation:** Option A (Rust bridge) for MVP, then migrate to Option B later.

---

## Success Metrics (Sprint 2)

- [ ] 12 integration tests passing
- [ ] Discover doctests from `.spl`, `.md`, `.sdt` files
- [ ] Exclude patterns work correctly
- [ ] Line number tracking accurate
- [ ] CLI `simple test --doctest --list` shows discovered tests
- [ ] CLI `simple test --doctest` runs discovered tests
- [ ] Unified output with BDD specs

---

## Open Questions

1. **Interpreter API:** What's the stable API for executing Simple code from Simple?
   - Need: `execute_line(context, code) -> Result[String, Error]`
   - Current: Placeholder stub in runner.spl

2. **File I/O:** When will `std.io` be ready?
   - Temporary solution: Rust FFI bridge
   - Long-term: Pure Simple stdlib

3. **BDD Integration:** Is `std.spec` ready for hooks?
   - Need: Registration API for external test sources
   - Current: Placeholder types in integration.spl

4. **Coverage Attribution:** How to map executed lines to public functions?
   - Need: Symbol table from compiler (`symbols.json`)
   - Need: Line-level coverage from interpreter/LLVM

---

## References

- **Spec:** `doc/spec/sdoctest.md` - Full specification
- **Integration:** `doc/doctest_integration.md` - BDD integration plan
- **Tests:** `test/unit/doctest/` - Unit tests
- **Fixtures:** `test/fixtures/doctest/` - Test data
- **Code:** `lib/std/doctest/` - Implementation

---

**Status Summary:**
- **Sprint 1:** ✅ Complete (Parser, Matcher, Runner, 40+ tests)
- **Sprint 2:** ⏳ 40% complete (Discovery framework, integration tests written, needs I/O bridge)
- **Sprint 3:** 📋 Planned (Advanced features)
- **Sprint 4:** 📋 Planned (Coverage and polish)
