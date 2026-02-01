# Test Writing Skill

## Test Levels

| Level | Mock Policy | Coverage Metric | Command |
|-------|-------------|-----------------|---------|
| Unit | All mocks allowed | Branch/Condition | `simple build test --level=unit` |
| Integration | HAL-only mocks | Public func coverage | `simple build test --level=integration` |
| System | No mocks | Class/struct method | `simple build test --level=system` |
| Environment | HAL/External/Lib | Branch/Condition | `simple build test --level=env` |

## Critical Rules

**NEVER ignore tests without explicit user approval:**
- Do NOT add `#[ignore]` without asking
- Do NOT comment out test code
- Do NOT skip failing tests as a "fix"
- ALWAYS fix root cause or ask user

## Running Tests

### Rust Tests
```bash
simple build rust test                         # All Rust tests
simple build rust test -p simple-driver        # Specific crate
simple build rust test -p simple-driver runner # Pattern match
simple build test                              # All tests (Rust + Simple)
```

### Simple (.spl) Tests
```bash
# Via simple build (auto-discovered)
simple build rust test -p simple-driver simple_stdlib
simple build rust test -p simple-driver simple_stdlib_unit
simple build rust test -p simple-driver simple_stdlib_system

# Direct interpreter
./rust/target/debug/simple src/std/test/unit/core/arithmetic_spec.spl
```

## Writing Rust Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_feature_works() {
        let result = feature();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_edge_case() {
        // Test edge cases explicitly
    }
}
```

## Writing Simple BDD Tests

Tests go in `src/std/test/{unit|system|integration}/`

**CRITICAL: Use docstring markdown, NOT println() for test documentation!**

```simple
# feature_spec.spl
import spec

describe "Feature":
    """
    # Feature Module

    Provides core functionality for X, Y, Z.

    ## Overview
    - Feature A does X
    - Feature B does Y

    ## Usage
    ```simple
    val f = Feature.new(10)
    f.increment()
    ```
    """

    context "when initialized":
        """
        Tests default initialization behavior.
        Ensures all fields start with correct values.
        """

        it "should have default value":
            """
            Default constructor should initialize value to 0.

            **Expected:** value = 0
            **Actual:** Verified via expect() assertion
            """
            let f = Feature.new()
            expect(f.value).to(equal(0))

    context "with operations":
        """
        Tests arithmetic operations on Feature.

        ## Tested Operations
        - increment(): adds 1
        - decrement(): subtracts 1
        - add(n): adds n
        """

        before_each:
            self.f = Feature.new(10)

        it "should increment":
            """
            Increment operation should add 1 to current value.

            Given: Feature with value 10
            When: increment() is called
            Then: value should be 11
            """
            self.f.increment()
            expect(self.f.value).to(equal(11))
```

**Documentation Guidelines:**
- **Every `describe` block**: Rich markdown overview with usage examples
- **Every `context` block**: Explain what scenario/condition is being tested
- **Every `it` block**: Document expected behavior, inputs, outputs
- **Use markdown**: Headers, lists, code blocks, tables
- **NO println()**: All explanations go in docstrings, not print statements
- **Auto-generate docs**: SSpec uses docstrings for spec documentation

## Test File Naming

- Rust: `*_tests.rs` in `tests/` or `mod tests` in source
- Simple: `*_spec.spl` or `*_test.spl`

## Matchers Reference

| Matcher | Usage |
|---------|-------|
| `equal(val)` | `expect(x).to(equal(5))` |
| `be_true()` | `expect(x).to(be_true())` |
| `be_false()` | `expect(x).to(be_false())` |
| `be_nil()` | `expect(x).to(be_nil())` |
| `be_greater_than(n)` | `expect(x).to(be_greater_than(5))` |
| `be_less_than(n)` | `expect(x).to(be_less_than(10))` |
| `contain(item)` | `expect(list).to(contain(5))` |
| `have_length(n)` | `expect(list).to(have_length(3))` |
| `match_regex(pat)` | `expect(s).to(match_regex("\\d+"))` |
| `raise_error(type)` | `expect(fn).to(raise_error(ValueError))` |

## Coverage

```bash
simple build coverage              # HTML report
simple build coverage --level=unit # Unit coverage
simple build coverage --level=all  # All reports
```

Target: 100% coverage for all levels.

## See Also

- `doc/test.md` - Full test policy
- `doc/system_test.md` - System test framework
- `doc/spec/testing/` - Testing framework specs
