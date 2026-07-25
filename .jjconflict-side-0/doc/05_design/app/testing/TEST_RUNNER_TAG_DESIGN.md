# Test Runner Tag Integration Design
#
# Design document for integrating @coverage, @longrun, @ci_only tags
# with the Simple test runner.

## Overview

The test runner needs to support filtering tests by tags:
- **Default run**: Excludes @coverage, @longrun, @ci_only
- **CI run**: Includes @coverage, @ci_only but excludes @longrun
- **Nightly run**: Includes all tags

## Tag Definitions

```simple
# Built-in test tags
enum TestTag:
    default         # Regular tests, always run
    coverage        # Coverage validation tests
    longrun         # Long-running tests (> 1 minute)
    ci_only         # CI-only tests
    integration     # Integration tests
    performance     # Performance benchmarks
    smoke           # Quick smoke tests
```

## Tag Attributes

Tests can be tagged using attributes:

```simple
# Single tag
@coverage
describe "Coverage tests":
    ...

# Multiple tags
@coverage @longrun
describe "Long coverage tests":
    ...

# Tag with parameter (future)
@timeout(60)
describe "Timed tests":
    ...
```

## Test Runner CLI

```bash
# Default run (excludes coverage, longrun, ci_only)
simple test

# Include coverage tests
simple test --tags coverage

# Include all CI tests
simple test --tags coverage,ci_only

# Exclude specific tags
simple test --exclude longrun

# Include only specific tags
simple test --only coverage

# Include everything (nightly)
simple test --tags "*"

# Verbose tag info
simple test -v --show-tags
```

## Environment Variables

```bash
# Alternative to CLI options
export SIMPLE_TEST_TAGS="+coverage,+ci_only"
export SIMPLE_TEST_EXCLUDE_TAGS="longrun"

# For CI pipelines
export SIMPLE_TEST_MODE=ci       # coverage,ci_only
export SIMPLE_TEST_MODE=nightly  # all tags
```

## Configuration File

```json
// simple.json
{
  "test": {
    "default": {
      "include": ["default", "smoke"],
      "exclude": ["coverage", "longrun", "ci_only"]
    },
    "ci": {
      "include": ["default", "coverage", "ci_only", "integration"],
      "exclude": ["longrun"]
    },
    "nightly": {
      "include": ["*"],
      "exclude": []
    }
  }
}
```

## Tag Detection Implementation

```simple
# In test runner
fn parse_tags(source: text) -> [TestTag]:
    """Extract tags from test source code."""
    var tags: [TestTag] = []
    
    val lines = source.split("\n")
    for line in lines:
        val trimmed = line.trim()
        
        # Check for tag attributes
        if trimmed.starts_with("@coverage"):
            tags.push(TestTag.coverage)
        elif trimmed.starts_with("@longrun"):
            tags.push(TestTag.longrun)
        elif trimmed.starts_with("@ci_only"):
            tags.push(TestTag.ci_only)
        elif trimmed.starts_with("@integration"):
            tags.push(TestTag.integration)
        elif trimmed.starts_with("@performance"):
            tags.push(TestTag.performance)
        elif trimmed.starts_with("@smoke"):
            tags.push(TestTag.smoke)
    
    # Default tag if none specified
    if tags.is_empty():
        tags.push(TestTag.default)
    
    tags

fn should_run_test(test_tags: [TestTag], config: TestConfig) -> bool:
    """Determine if test should run based on tags and config."""
    
    # Check excludes first
    for tag in test_tags:
        if config.exclude.contains(tag):
            return false
    
    # Check includes
    if config.include.contains("*"):
        return true
    
    for tag in test_tags:
        if config.include.contains(tag):
            return true
    
    false
```

## Coverage Tag Enforcement

```simple
# In std.coverage module
var _test_has_coverage_tag = false

fn _check_coverage_tag_from_source():
    """Check if current test file has @coverage tag."""
    val test_file = TestContext.current_file()
    val source = rt_file_read(test_file)
    
    _test_has_coverage_tag = source.contains("@coverage") or 
                              source.contains("coverage_describe") or
                              source.contains("coverage_it")

fn validate_coverage_access():
    """Validate coverage API can be called."""
    if not _test_has_coverage_tag and not _coverage_tag_enabled:
        raise CoverageNotEnabledException(
            "check_coverage() requires @coverage tag. "
            "Add @coverage attribute or use coverage_describe/coverage_it."
        )
```

## CI/CD Integration

### GitHub Actions

```yaml
name: Tests

on: [push, pull_request]

jobs:
  quick:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Quick tests
        run: simple test  # default: excludes coverage, longrun

  full:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Generate coverage
        run: simple test --coverage
      - name: Run coverage tests
        run: |
          export SIMPLE_TEST_TAGS="+coverage,+ci_only"
          simple test

  nightly:
    runs-on: ubuntu-latest
    if: github.event_name == 'schedule'
    steps:
      - uses: actions/checkout@v3
      - name: All tests
        run: simple test --tags "*"
```

### GitLab CI

```yaml
stages:
  - quick
  - full
  - nightly

quick_tests:
  stage: quick
  script:
    - simple test

coverage_tests:
  stage: full
  script:
    - simple test --coverage
    - SIMPLE_TEST_TAGS="+coverage" simple test

nightly_tests:
  stage: nightly
  only:
    - schedules
  script:
    - simple test --tags "*"
```

## Test Output with Tags

```
$ simple test --tags coverage -v

Running tests with tags: [coverage]
Excluding tags: []

[coverage] src/lib/test/coverage_spec.spl
  Coverage API Availability
    it blocks check_coverage without @coverage tag ... ok
    it allows check_coverage with @coverage tag ... ok
  Coverage Types
    it supports line coverage type ... ok
    it supports branch coverage type ... ok
    ...

[coverage,longrun] src/lib/test/grammar_coverage_spec.spl
  (skipped - tag 'longrun' excluded)

Tests: 45 passed, 2 skipped, 0 failed
Tags: coverage=45, longrun=2 (skipped)
```

## Implementation Timeline

### Phase 1: Basic Tag Support
- [ ] Parse @tag attributes from source
- [ ] Add --tags CLI option
- [ ] Implement tag filtering

### Phase 2: Coverage Integration
- [ ] Enforce @coverage tag for check_coverage()
- [ ] Add coverage_describe/coverage_it helpers
- [ ] Test error messages

### Phase 3: CI Integration
- [ ] Add configuration file support
- [ ] Create CI workflow templates
- [ ] Document best practices

### Phase 4: Advanced Features
- [ ] Tag combinations (and/or/not)
- [ ] Custom tag definitions
- [ ] Tag statistics and reports
