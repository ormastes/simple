# Skipped Tests Analysis - 2026-01-21

## Summary

The codebase contains **1,241 skipped tests** across **116 test files**. These are tests marked with `skip` in the SSpec framework, indicating features that are planned but not yet implemented.

## Key Statistics

- **Total skipped tests**: 1,241
- **Files with skipped tests**: 116
- **Percentage of test files**: ~15% (116 out of ~700+ test files)

## Distribution by Directory

| Directory | Skip Count | Category |
|-----------|-----------|----------|
| `test/lib/std/unit/core` | 133 | Core language features |
| `test/lib/std/unit/sdn` | 71 | SDN (Simple Data Notation) |
| `test/lib/std/unit/ml` | 50 | Machine learning features |
| `test/lib/std/unit/verification` | 26 | Formal verification |
| `test/lib/std/unit/spec` | 21 | Testing framework itself |
| `test/lib/std/unit/concurrency` | 9 | Concurrency features |
| `test/integration` | 4 | Integration tests |
| `test/unit/spec` | 1 | Unit tests |
| **Other directories** | ~926 | Various stdlib modules |

## Top 20 Files with Most Skipped Tests

| Count | File | Category |
|-------|------|----------|
| 59 | `simple/std_lib/test/unit/testing/helpers_spec.spl` | Test helpers |
| 51 | `simple/std_lib/test/unit/set_spec.spl` | Set data structure |
| 34 | `test/lib/std/unit/core/regex_spec.spl` | Regular expressions |
| 29 | `test/lib/std/unit/core/math_spec.spl` | Math operations |
| 29 | `test/lib/std/system/improvements/stdlib_improvements_spec.spl` | Stdlib improvements |
| 28 | `test/lib/std/unit/tooling/tooling_spec.spl` | Development tooling |
| 27 | `test/lib/std/system/spec/arch_spec.spl` | Architecture tests |
| 27 | `test/lib/std/system/gherkin/gherkin_spec.spl` | Gherkin BDD |
| 27 | `simple/std_lib/test/unit/testing/mock_spec.spl` | Mocking framework |
| 26 | `test/lib/std/unit/verification/memory_capabilities_spec.spl` | Memory safety |
| 25 | `test/lib/std/unit/sdn/lexer_spec.spl` | SDN lexer |
| 24 | `test/lib/std/integration/ui/tui/ratatui_backend_spec.spl` | TUI framework |
| 23 | `test/lib/std/system/property/generators_spec.spl` | Property testing |
| 22 | `test/lib/std/system/snapshot/formats_spec.spl` | Snapshot testing |
| 22 | `simple/std_lib/test/unit/testing/smoke_test_spec.spl` | Smoke tests |
| 22 | `simple/std_lib/test/unit/testing/contract_spec.spl` | Contract testing |
| 21 | `test/lib/std/unit/spec/given_working_spec.spl` | Given/When/Then |
| 21 | `test/lib/std/unit/cli_spec.spl` | CLI features |
| 19 | `test/lib/std/unit/host/datetime_spec.spl` | DateTime API |
| 18 | `test/lib/std/unit/sdn/value_spec.spl` | SDN values |

## Common Skip Reasons (Sample)

Based on a sample of skip messages:
- **"not yet implemented"** - Feature planned but not started
- **"not implemented"** - Alternative phrasing of above
- **"pending"** - Test written, implementation pending

## Example Skipped Tests

### Testing Framework (`helpers_spec.spl` - 59 skips)
Test helpers and assertion utilities that are planned but not yet built.

### Set Data Structure (`set_spec.spl` - 51 skips)
Complete Set<T> implementation including:
- Construction, insertion, removal
- Set operations (union, intersection, difference)
- Iteration and conversion

### Regular Expressions (`regex_spec.spl` - 34 skips)
Advanced regex features beyond basic matching.

### Math Operations (`math_spec.spl` - 29 skips)
Extended math functions and numeric operations.

### ML Features (`ml/` - 50 skips total)
Machine learning framework components including:
- Tensor operations
- Neural network layers
- Training utilities

## Comparison: Skipped vs Ignored

| Type | Count | Purpose | How to Run |
|------|-------|---------|-----------|
| **Skipped** (skip tag) | 1,241 | Not yet implemented | Won't run even if targeted |
| **Ignored** (#[ignore]) | 2 | Too slow (120+ sec) | `cargo test -- --ignored` |

## Impact on Test Coverage

- **Total tests in codebase**: 7,909
- **Skipped tests**: 1,241 (15.7%)
- **Actually running**: 6,668 (84.3%)

The high number of skipped tests indicates:
1. **Active planning**: Many features are designed with tests before implementation
2. **Test-driven development**: Tests written first, implementation follows
3. **Transparency**: Clear visibility into what's planned vs implemented

## Using the New Features to List Skipped Tests

With the newly implemented `--only-skipped` flag:

```bash
# List all skipped tests
simple test --list --only-skipped

# Count skipped tests
simple test --list --only-skipped | grep "Total:"

# List skipped tests in specific category
simple test --list --only-skipped --tag unit

# List skipped regex tests
simple test --list --only-skipped regex
```

## Recommendations

### For Development Priority

Focus on files with highest skip counts:
1. **Testing helpers** (59 skips) - Core testing infrastructure
2. **Set<T>** (51 skips) - Common data structure
3. **Regex** (34 skips) - Commonly needed feature
4. **Math** (29 skips) - Frequently used utilities

### For Documentation

Skipped tests serve as:
- Feature roadmap
- API design documentation
- Usage examples (even before implementation)

### For CI/CD

Monitor skip counts over time:
```bash
# Generate skip report
simple test --list --only-skipped > doc/report/skipped_tests.txt

# Track progress
git diff doc/report/skipped_tests.txt
```

## Conclusion

The 1,241 skipped tests represent a well-planned feature roadmap. They demonstrate:
- **Test-first mindset**: Tests define APIs before implementation
- **Clear priorities**: High skip counts indicate feature demand
- **Organized development**: Skipped tests provide implementation checklist

The new `--only-skipped` flag makes it easy to:
- Identify unimplemented features
- Prioritize development work
- Track implementation progress
