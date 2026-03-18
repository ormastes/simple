# Per-Test Coverage Contracts

## Problem

When a developer uses a temporary shortcut (e.g., in-memory cache instead of Redis), aggregate coverage can mask that the preferred component is never tested. No existing tool binds a *specific test file* to *specific source targets* with quantitative enforcement.

## Solution

First-class per-test coverage contracts: declarative annotations in test spec files that specify which source files/functions the test must cover and to what threshold. Contracts appear as virtual test cases in output (pass/fail alongside regular `it` blocks).

## Syntax

```simple
# @covers src/lib/common/array.spl 80%
# @covers src/lib/common/array_advanced.spl 90%
# @covers_fn src/lib/common/array.spl array_position array_find
# @not_covers src/lib/common/string.spl
```

| Directive | Meaning |
|-----------|---------|
| `# @covers <path> <N>%` | Target file must reach N% decision coverage from this test |
| `# @covers <path>` | Target file must be touched (coverage > 0%) |
| `# @covers_fn <path> <fn1> <fn2>` | Named functions must have decisions covered |
| `# @not_covers <path>` | Negative: test must NOT touch target file |

## Novelty Analysis

| Feature | Simple | Istanbul | Coverlet | pytest-cov | JaCoCo |
|---------|--------|----------|----------|------------|--------|
| Per-file threshold | Yes | No | No | No | No |
| Function-level contracts | Yes | No | No | No | No |
| Negative contracts | Yes | No | No | No | No |
| Comment-based syntax | Yes | N/A | N/A | N/A | N/A |
| Virtual test case output | Yes | No | No | No | No |
| Per-test-file SDN dump | Yes | No | No | No | No |

No existing coverage tool supports binding a specific test file to specific source targets with quantitative enforcement and negative constraints. This is a novel contribution.

## Design Rationale

1. **Comment-based directives** - Consistent with existing `# @tag`, `# @req` patterns. No parser changes needed for the Simple language itself.
2. **Suffix-based path matching** - SDN coverage data uses full paths while directives use relative paths. Suffix matching handles both.
3. **Virtual test cases** - Contract results appear alongside regular `it` blocks in test output, making failures immediately visible without separate tooling.
4. **Per-file SDN dump** - Coverage data is dumped after each test file (when contracts exist) to evaluate contracts against that file's coverage contribution.
5. **Function-level resolution** - Uses source file AST parsing to find function line ranges, then cross-references with SDN decision line numbers.

## Implementation

- **Parser**: `extract_coverage_contracts()` in `test_analyzer.rs`
- **Data model**: `CoverageContract` in `test_meta.rs`, `CoverageContractResult` in `types.rs`
- **Validation**: `contract_validator.rs` with `validate_contracts()` entry point
- **Integration**: `runner.rs` validates after each test file when coverage is enabled
- **Registry**: `StaticTestRegistry` indexes contracts by file path

## Outcome

Forgotten shortcuts become structurally impossible to ignore. System tests enforce architectural intent through coverage obligations.
