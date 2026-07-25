# Coverage Check API Design Document

## Overview

Design a `check_coverage()` API for Simple language spec tests that validates coverage thresholds during test execution. This API is only available when coverage test tag is enabled, preventing accidental use in regular tests.

## Requirements

### 1. Core Requirements
1. **API**: `check_coverage(coverage_type, pattern, minimum/maximum, minimum_check=true)`
2. **Tag-Gated**: Only available when `@coverage` tag is enabled on test
3. **Pattern Matching**: Support file/function pattern matching (glob, regex)
4. **Threshold Types**: Support minimum and maximum thresholds
5. **Coverage Types**: line, branch, function, region coverage

### 2. Test Categories
- **Default Tests**: Run by developers locally, exclude coverage tests
- **CI Tests**: Include coverage tests, longrun tests
- **Coverage Tests**: Marked with `@coverage` tag, run in CI only

### 3. Grammar Design

```simple
# Tag-based test marking
@coverage
@longrun
@ci_only
describe "Coverage tests":
    it "checks line coverage":
        check_coverage("line", "src/parser/*.spl", minimum: 80.0)
    
    it "checks branch coverage":
        check_coverage("branch", "src/**/*.spl", minimum: 70.0, maximum: 100.0)
```

## API Specification

### `check_coverage(coverage_type, pattern, minimum, maximum, minimum_check)`

**Parameters:**
- `coverage_type: string` - Type of coverage to check
  - `"line"` - Line coverage percentage
  - `"branch"` - Branch coverage percentage
  - `"function"` - Function coverage percentage
  - `"region"` - Region coverage (LLVM-style)
  
- `pattern: string` - Glob pattern for files to check
  - `"src/*.spl"` - All .spl files in src/
  - `"src/**/*.spl"` - All .spl files recursively
  - `"src/parser/ast.spl"` - Specific file
  - `"**/test_*.spl"` - All test files

- `minimum: f64` - Minimum coverage threshold (0.0 - 100.0)
  - Required when `minimum_check=true`
  - Test fails if actual coverage < minimum

- `maximum: f64` - Maximum coverage threshold (0.0 - 100.0)
  - Optional, default is 100.0
  - Test fails if actual coverage > maximum
  - Useful for detecting dead code

- `minimum_check: bool` - Check mode (default: true)
  - `true`: Fail if coverage < minimum
  - `false`: Fail if coverage > maximum (inverse check)

**Returns:** `CoverageResult`
- `passed: bool` - Whether check passed
- `actual: f64` - Actual coverage percentage
- `threshold: f64` - Threshold that was checked
- `files_matched: i32` - Number of files matching pattern
- `details: [FileResult]` - Per-file breakdown

**Errors:**
- `CoverageNotEnabledException` - Called without `@coverage` tag
- `InvalidPatternException` - Invalid glob pattern
- `NoFilesMatchedException` - Pattern matched no files
- `CoverageDataNotFoundException` - No coverage data available

### Example Usage

```simple
use std.spec.*
use std.coverage.*

# Regular test - coverage API NOT available
describe "Basic math":
    it "adds numbers":
        expect 1 + 1 == 2
        # check_coverage("line", "*", 80.0)  # ERROR: CoverageNotEnabledException

# Coverage test - API available
@coverage
describe "Coverage validation":
    it "validates parser coverage":
        # Check minimum line coverage
        val result = check_coverage("line", "src/parser/**/*.spl", 
                                    minimum: 80.0)
        expect result.passed
        
    it "validates branch coverage":
        # Check minimum branch coverage
        check_coverage("branch", "src/compiler/*.spl", 
                       minimum: 70.0, maximum: 95.0)
        
    it "detects dead code":
        # Check for over-coverage (dead code detection)
        check_coverage("line", "src/deprecated/*.spl", 
                       maximum: 5.0, minimum_check: false)

# Long-running coverage test - CI only
@coverage
@longrun
describe "Full coverage suite":
    it "validates entire codebase":
        check_coverage("line", "src/**/*.spl", minimum: 85.0)
        check_coverage("branch", "src/**/*.spl", minimum: 75.0)
        check_coverage("function", "src/**/*.spl", minimum: 90.0)
```

## Tag System Design

### Tag Definitions

```simple
# In std.spec module
enum TestTag:
    default       # Default tests, run locally
    coverage      # Coverage tests, requires coverage data
    longrun       # Long-running tests, CI only
    ci_only       # CI-only tests
    integration   # Integration tests
    performance   # Performance benchmarks
    smoke         # Smoke tests (quick sanity check)

# Tag macro attributes
@coverage      # Equivalent to @tag(TestTag.coverage)
@longrun       # Equivalent to @tag(TestTag.longrun)
@ci_only       # Equivalent to @tag(TestTag.ci_only)
```

### Test Filtering Logic

```simple
# Test runner configuration
val test_config = TestConfig {
    # Default run (local development)
    include_tags: [TestTag.default, TestTag.smoke]
    exclude_tags: [TestTag.coverage, TestTag.longrun, TestTag.ci_only]
    
    # CI run
    # include_tags: [TestTag.default, TestTag.coverage, TestTag.ci_only]
    # exclude_tags: []
    
    # Full CI run (including longrun)
    # include_tags: [*]
    # exclude_tags: []
}
```

### Environment-Based Tag Control

```bash
# Local development (default)
simple test

# CI pipeline (include coverage tests)
SIMPLE_TEST_TAGS="+coverage,+ci_only" simple test

# Full CI (include long-running)
SIMPLE_TEST_TAGS="+coverage,+longrun,+ci_only" simple test

# Nightly build (everything)
SIMPLE_TEST_TAGS="*" simple test

# Run only coverage tests
SIMPLE_TEST_TAGS="coverage" simple test
```

## Implementation Architecture

### 1. Tag Validation Layer

```simple
# In std.coverage module
fn check_coverage_allowed() -> bool:
    # Check if current test has @coverage tag
    val current_test = TestContext.current()
    return current_test.has_tag(TestTag.coverage)

fn validate_coverage_access():
    if not check_coverage_allowed():
        raise CoverageNotEnabledException(
            "check_coverage() can only be called in tests marked with @coverage tag. "
            "Add @coverage attribute to your test to enable coverage APIs."
        )
```

### 2. Coverage Data Reader

```simple
# In std.coverage module
struct CoverageData:
    format: string           # "llvm", "lcov", "json"
    timestamp: i64
    files: [FileCoverage]
    
struct FileCoverage:
    path: string
    lines_total: i32
    lines_covered: i32
    branches_total: i32
    branches_covered: i32
    functions_total: i32
    functions_covered: i32
    regions: [RegionCoverage]

fn load_coverage_data() -> CoverageData:
    # Load from environment-specified path
    val cov_path = env("SIMPLE_COVERAGE_DATA") 
                   ?? ".coverage/coverage.json"
    
    if not Path(cov_path).exists():
        raise CoverageDataNotFoundException(
            f"Coverage data not found at '{cov_path}'. "
            "Run tests with coverage enabled first."
        )
    
    return CoverageData.from_file(cov_path)
```

### 3. Pattern Matcher

```simple
# In std.coverage module
fn match_files(pattern: string, files: [FileCoverage]) -> [FileCoverage]:
    val glob = Glob.compile(pattern)
    return files.filter(\f: glob.matches(f.path))
```

### 4. Coverage Calculator

```simple
# In std.coverage module
fn calculate_coverage(cov_type: string, files: [FileCoverage]) -> f64:
    match cov_type:
        "line":
            val total = files.map(\f: f.lines_total).sum()
            val covered = files.map(\f: f.lines_covered).sum()
            if total == 0: return 100.0
            return (covered as f64 / total as f64) * 100.0
            
        "branch":
            val total = files.map(\f: f.branches_total).sum()
            val covered = files.map(\f: f.branches_covered).sum()
            if total == 0: return 100.0
            return (covered as f64 / total as f64) * 100.0
            
        "function":
            val total = files.map(\f: f.functions_total).sum()
            val covered = files.map(\f: f.functions_covered).sum()
            if total == 0: return 100.0
            return (covered as f64 / total as f64) * 100.0
            
        "region":
            # LLVM-style region coverage
            val total = files.flat_map(\f: f.regions).len()
            val covered = files.flat_map(\f: f.regions)
                              .filter(\r: r.count > 0).len()
            if total == 0: return 100.0
            return (covered as f64 / total as f64) * 100.0
            
        _:
            raise InvalidCoverageTypeException(f"Unknown coverage type: {cov_type}")
```

### 5. Main API Implementation

```simple
# In std.coverage module
fn check_coverage(
    coverage_type: string,
    pattern: string,
    minimum: f64 = 0.0,
    maximum: f64 = 100.0,
    minimum_check: bool = true
) -> CoverageResult:
    # 1. Validate access
    validate_coverage_access()
    
    # 2. Load coverage data
    val data = load_coverage_data()
    
    # 3. Match files
    val matched = match_files(pattern, data.files)
    if matched.is_empty():
        raise NoFilesMatchedException(
            f"Pattern '{pattern}' matched no files in coverage data."
        )
    
    # 4. Calculate coverage
    val actual = calculate_coverage(coverage_type, matched)
    
    # 5. Check threshold
    val passed = if minimum_check:
        actual >= minimum
    else:
        actual <= maximum
    
    val threshold = if minimum_check: minimum else: maximum
    
    # 6. Build result
    val result = CoverageResult {
        passed: passed
        actual: actual
        threshold: threshold
        files_matched: matched.len()
        coverage_type: coverage_type
        pattern: pattern
        minimum_check: minimum_check
        details: matched.map(\f: FileResult {
            path: f.path
            coverage: calculate_file_coverage(coverage_type, f)
        })
    }
    
    # 7. Report and assert
    if not passed:
        val msg = if minimum_check:
            f"Coverage check failed: {coverage_type} coverage for '{pattern}' "
            f"is {actual:.1f}% (minimum: {minimum:.1f}%)"
        else:
            f"Coverage check failed: {coverage_type} coverage for '{pattern}' "
            f"is {actual:.1f}% (maximum: {maximum:.1f}%)"
        
        # Print details
        println(msg)
        println("Files below threshold:")
        for file in result.details.filter(\f: not f.meets_threshold(threshold, minimum_check)):
            println(f"  {file.path}: {file.coverage:.1f}%")
        
        # Fail test
        expect false, msg
    
    return result
```

## Test Runner Modifications

### Command Line Interface

```bash
# Default run (excludes coverage, longrun)
simple test

# Include coverage tests
simple test --tags coverage

# Include all CI tests
simple test --tags coverage,ci_only

# Include everything
simple test --tags "*"

# Exclude specific tags
simple test --exclude-tags longrun

# Run only specific tagged tests
simple test --only-tags coverage
```

### Configuration File

```json
// simple.json
{
  "test": {
    "default_tags": ["default", "smoke"],
    "ci_tags": ["default", "coverage", "ci_only", "integration"],
    "nightly_tags": ["*"],
    "exclude_default": ["coverage", "longrun", "ci_only"]
  }
}
```

## CI/CD Integration

### GitHub Actions Example

```yaml
name: Tests

on: [push, pull_request]

jobs:
  # Quick tests for PRs
  quick-test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Run quick tests
        run: simple test --tags default,smoke
  
  # Full tests with coverage
  full-test:
    runs-on: ubuntu-latest
    needs: quick-test
    steps:
      - uses: actions/checkout@v3
      
      - name: Run tests with coverage
        run: |
          simple test --coverage --tags default,coverage,ci_only
      
      - name: Upload coverage
        uses: actions/upload-artifact@v3
        with:
          name: coverage
          path: .coverage/
  
  # Nightly full suite (including longrun)
  nightly:
    runs-on: ubuntu-latest
    if: github.event_name == 'schedule'
    steps:
      - uses: actions/checkout@v3
      - name: Run all tests
        run: simple test --coverage --tags "*"
```

## Error Messages

### CoverageNotEnabledException
```
Error: CoverageNotEnabledException

check_coverage() can only be called in tests marked with @coverage tag.

To fix this:
1. Add @coverage attribute to your test:

   @coverage
   describe "My coverage tests":
       it "checks coverage":
           check_coverage("line", "src/**/*.spl", minimum: 80.0)

2. Or run tests with coverage tag enabled:
   simple test --tags coverage

Note: Coverage tests are excluded from default test runs.
Run 'simple test --tags coverage' to include them.
```

### CoverageDataNotFoundException
```
Error: CoverageDataNotFoundException

Coverage data not found at '.coverage/coverage.json'.

To generate coverage data:
1. Run tests with coverage enabled:
   simple test --coverage

2. Or set SIMPLE_COVERAGE_DATA environment variable:
   export SIMPLE_COVERAGE_DATA=/path/to/coverage.json
```

### NoFilesMatchedException
```
Error: NoFilesMatchedException

Pattern 'src/nonexistent/**/*.spl' matched no files in coverage data.

Available files in coverage data:
  - src/parser/ast.spl
  - src/parser/lexer.spl
  - src/compiler/codegen.spl
  ...

Hint: Check your pattern syntax:
  - Use ** for recursive matching
  - Use * for single directory level
  - Patterns are relative to project root
```

## Implementation Plan

### Phase 1: Core Infrastructure (Week 1)
- [ ] Implement tag system in test runner
- [ ] Add tag validation for coverage API
- [ ] Create CoverageNotEnabledException
- [ ] Write tag system tests

### Phase 2: Coverage Data Layer (Week 1)
- [ ] Implement coverage data reader (JSON, LCOV)
- [ ] Add pattern matching (glob)
- [ ] Create coverage calculator
- [ ] Write data layer tests

### Phase 3: Check API (Week 2)
- [ ] Implement check_coverage() function
- [ ] Add threshold validation
- [ ] Create result reporting
- [ ] Write API tests

### Phase 4: Test Runner Integration (Week 2)
- [ ] Add --tags CLI option
- [ ] Add --exclude-tags CLI option
- [ ] Add --only-tags CLI option
- [ ] Update configuration file format

### Phase 5: CI/CD Integration (Week 3)
- [ ] Create CI workflow templates
- [ ] Add coverage artifact upload
- [ ] Create coverage badge generation
- [ ] Write integration tests

### Phase 6: Documentation & Examples (Week 3)
- [ ] Write API documentation
- [ ] Create example tests
- [ ] Update README
- [ ] Create migration guide

## Summary

This design provides:

1. **check_coverage() API** - Validates coverage thresholds with pattern matching
2. **Tag System** - Controls which tests run in which environment
3. **Safety** - API only available when @coverage tag is enabled
4. **Flexibility** - Multiple coverage types, patterns, threshold modes
5. **CI/CD Ready** - Designed for integration with CI pipelines
6. **Clear Errors** - Helpful error messages with fix suggestions

The key insight is that coverage tests are:
- **Not default tests** - They require coverage data
- **CI tests** - Run automatically in CI pipeline
- **Gated** - API throws exception if used without @coverage tag
- **Long-running option** - Some coverage tests are @longrun for nightly builds
