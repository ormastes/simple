# Test Writing Skill

## Test Levels

| Level | Mock Policy | Coverage Metric | Command |
|-------|-------------|-----------------|---------|
| Unit | All mocks allowed | Branch/Condition | `make test-unit` |
| Integration | HAL-only mocks | Public func coverage | `make test-it` |
| System | No mocks | Class/struct method | `make test-system` |
| Environment | HAL/External/Lib | Branch/Condition | `make test-env` |

## Critical Rules

**NEVER ignore tests without explicit user approval:**
- Do NOT add `#[ignore]` without asking
- Do NOT comment out test code
- Do NOT skip failing tests as a "fix"
- ALWAYS fix root cause or ask user

## Running Tests

### Rust Tests
```bash
cargo test --workspace              # All tests
cargo test -p simple-driver         # Specific crate
cargo test -p simple-driver runner  # Pattern match
make test                           # Via Makefile
```

### Simple (.spl) Tests
```bash
# Via cargo (auto-discovered)
cargo test -p simple-driver simple_stdlib
cargo test -p simple-driver simple_stdlib_unit
cargo test -p simple-driver simple_stdlib_system

# Direct interpreter
./target/debug/simple simple/std_lib/test/unit/core/arithmetic_spec.spl
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

Tests go in `simple/std_lib/test/{unit|system|integration}/`

```simple
# feature_spec.spl
import spec

describe "Feature":
    """Feature documentation."""

    context "when initialized":
        it "should have default value":
            let f = Feature.new()
            expect(f.value).to(equal(0))

    context "with operations":
        before_each:
            self.f = Feature.new(10)

        it "should increment":
            self.f.increment()
            expect(self.f.value).to(equal(11))
```

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
make coverage          # HTML report
make coverage-unit     # Unit coverage
make coverage-all      # All reports
```

Target: 100% coverage for all levels.

## See Also

- `doc/test.md` - Full test policy
- `doc/system_test.md` - System test framework
- `doc/spec/testing/` - Testing framework specs
