# Skip Test Analysis Report

Generated: 2026-01-22

## Executive Summary

**Total Skipped Tests: 772**
- Using `skip: true` parameter: 30
- Using `skip "reason"` function: 742

This represents tests that are not yet implemented or blocked on missing features.

## Breakdown by Test Type

| Test Type | Skip Count | Percentage |
|-----------|------------|------------|
| Unit Tests | 425 | 55.1% |
| System/Feature Tests | 293 | 38.0% |
| Integration Tests | 54 | 7.0% |

## Top Categories (Unit Tests)

| Category | Skip Count | Key Areas |
|----------|------------|-----------|
| **Parser/Tree-sitter** | 151 | Grammar compilation, language detection, incremental parsing |
| **DAP (Debug Adapter)** | 37 | Debug protocol, breakpoints, variable inspection |
| **ML/Torch** | 42 | Tensor operations, neural networks, CUDA integration |
| **Concurrency** | 30 | Promise API, async/await (blocked on async runtime) |
| **Tooling** | 28 | Build system, package manager, code generation |
| **SDN Format** | 28 | Parser, serializer, compatibility with Rust impl |
| **Verification** | 26 | Memory safety proofs, capability checking |
| **LSP** | 25 | Language server protocol, completions, diagnostics |
| **Testing Framework** | 22 | Contract testing, property-based testing |
| **Game Engine** | 20 | Physics, rendering, entity-component system |

## Top 20 Files with Most Skips

| File | Skips | Primary Reason |
|------|-------|----------------|
| `parser/treesitter/grammar_simple_spec.spl` | 80 | Tree-sitter grammar not complete |
| `concurrency/promise_spec.spl` | 30 | Async runtime not implemented |
| `tooling/tooling_spec.spl` | 28 | Build tooling pending |
| `spec/arch_spec.spl` | 27 | Architecture tests deferred |
| `verification/memory_capabilities_spec.spl` | 26 | Lean 4 verification pending |
| `improvements/stdlib_improvements_spec.spl` | 25 | Future stdlib enhancements |
| `ui/tui/ratatui_backend_spec.spl` | 24 | TUI framework not started |
| `property/generators_spec.spl` | 23 | Property testing generators |
| `snapshot/formats_spec.spl` | 22 | Snapshot testing formats |
| `testing/contract_spec.spl` | 22 | Contract testing framework |
| `sdn/cli_spec.spl` | 17 | SDN CLI tools |
| `property/shrinking_spec.spl` | 17 | Property test shrinking |
| `snapshot/comparison_spec.spl` | 16 | Snapshot diff algorithms |
| `ml/simple_math_integration_spec.spl` | 16 | ML integration tests |
| `dap/server_spec.spl` | 15 | DAP server implementation |
| `snapshot/runner_spec.spl` | 15 | Snapshot test runner |
| `snapshot/basic_spec.spl` | 15 | Basic snapshot tests |
| `dap/protocol_spec.spl` | 13 | DAP protocol messages |
| `sdn/file_io_spec.spl` | 13 | SDN file I/O |
| `property/runner_spec.spl` | 13 | Property test runner |

## Blocking Dependencies

### High Priority (>20 skips each)

1. **Async Runtime** (30 skips)
   - Files: `concurrency/promise_spec.spl`
   - Impact: Promise API, async/await syntax
   - Dependencies: Runtime executor, event loop

2. **Tree-sitter Integration** (151 skips)
   - Files: `parser/treesitter/*_spec.spl`
   - Impact: LSP, syntax highlighting, code navigation
   - Dependencies: Grammar compilation, incremental parsing

3. **Testing Infrastructure** (79 skips)
   - Files: `testing/*_spec.spl`, `property/*_spec.spl`, `snapshot/*_spec.spl`
   - Impact: Advanced testing capabilities
   - Dependencies: Property generators, snapshot storage

4. **Tooling** (28 skips)
   - Files: `tooling/tooling_spec.spl`
   - Impact: Build system, package management
   - Dependencies: Dependency resolution, build cache

### Medium Priority (10-20 skips each)

5. **DAP (Debug Adapter Protocol)** (37 skips)
   - Debugger integration, breakpoints, variable inspection

6. **SDN Format** (28 skips)
   - Data format parity with Rust implementation

7. **Verification** (26 skips)
   - Formal verification with Lean 4

8. **LSP** (25 skips)
   - Language server features

9. **Game Engine** (20 skips)
   - Physics, rendering, ECS

### Lower Priority (<10 skips each)

- Constraints solving (7 skips)
- Neural networks (6 skips)
- Collision detection (5 skips)
- Host platform features (3 skips)

## Sample Skipped Tests by Category

### Concurrency (30 skips)
All tests in `promise_spec.spl` are skipped with note:
> "All tests below are marked as skip until [async runtime] is resolved."

Examples:
- Promise creation (resolved, rejected, with executor)
- Promise chaining (then, map, flat_map, catch)
- Promise combinators (all, race, all_settled)
- Type preservation through promise chains

### Parser/Tree-sitter (151 skips)
- Grammar compilation and optimization
- Language detection from file extensions/shebangs
- Incremental parsing with edits
- Query system for syntax highlighting
- Error recovery strategies

### Testing Framework (79 skips)
- Contract-based testing
- Property-based testing with generators and shrinking
- Snapshot testing with comparison algorithms
- Test parameterization and fixtures

### Tooling (28 skips)
- Build system configuration
- Package dependency resolution
- Code generation from specs
- Project scaffolding

## Trends Over Time

| Date | Total Skips | Notes |
|------|-------------|-------|
| 2026-01-16 | 1,241 | From CLAUDE.md documentation |
| 2026-01-22 | 772 | Current count from source code |

**Difference: -469 skips** (37.8% reduction)

Possible explanations:
1. Tests were implemented/fixed
2. Some skipped tests were removed
3. Documentation count included duplicate/nested skips
4. Source code count is more accurate

## Recommendations

### Immediate Actions
1. **Verify async runtime roadmap** - 30 tests blocked
2. **Prioritize tree-sitter grammar** - 151 tests blocked
3. **Document skip reasons** - Many use generic "not implemented"

### Short Term (Next Sprint)
1. Implement basic Promise API stub for testing
2. Complete core tree-sitter grammar rules
3. Add more specific skip reasons with issue links

### Long Term
1. Reduce system/feature test skips (293 tests)
2. Complete DAP and LSP implementations
3. Build out testing infrastructure (property, snapshot)

## Methodology

**Data Collection:**
- Searched for `skip: true` parameter in `it` blocks
- Searched for `skip "reason"` function calls
- Excluded false positives (is_skipped, should_skip, etc.)

**Classification:**
- Extracted test area from file path
- Grouped by unit/integration/system/feature
- Counted by file and category

**Files Analyzed:**
- `test/**/*_spec.spl`
- `simple/std_lib/test/**/*_spec.spl`

---

*This report helps prioritize which skipped tests to implement first based on blocking dependencies and test area impact.*
