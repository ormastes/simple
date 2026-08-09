# BDD Tests for Mixin Features

This directory contains Behavior-Driven Development (BDD) tests for the Simple language mixin feature using Cucumber.

## Overview

The mixin feature allows composing behavior into classes without inheritance. These tests validate:
- Mixin declaration and application
- Generic type parameters with inference
- Trait bounds and required methods
- Field and method conflict detection
- Error handling and diagnostics

## Test Structure

### Feature Files
- `specs/features/mixin_basic.feature` - 12 scenarios for basic mixins
- `specs/features/mixin_generic.feature` - 14 scenarios for generic mixins

### Test Runner
- `main.rs` - Cucumber test harness with step definitions

### World State
```rust
pub struct MixinWorld {
    source_code: String,
    parse_result: Option<Result<Module, String>>,
    temp_file: Option<PathBuf>,
}
```

## Running Tests

### Build Tests
```bash
cargo build --test bdd_mixins
```

### Run All Scenarios
```bash
cargo test --test bdd_mixins
```

### Run Specific Feature
```bash
cargo test --test bdd_mixins -- --name "basic"
cargo test --test bdd_mixins -- --name "generic"
```

### Run Specific Scenario
```bash
cargo test --test bdd_mixins -- --scenario "Declare a simple mixin"
```

## Step Definitions

### Given Steps (Setup)
- `Given a file "X" with content:` - Create test file with code
- `Given the Simple compiler is available` - Verify compiler setup
- `Given the type checker is enabled` - Enable type checking
- `Given type inference is enabled` - Enable type inference

### When Steps (Actions)
- `When I parse the file` - Run parser on test file
- `When I compile the file` - Run full compilation
- `When I compile the file with type inference` - Compile with inference

### Then Steps (Assertions)
- `Then parsing should succeed` - Assert no parse errors
- `Then compilation should succeed` - Assert no compile errors
- `Then compilation should fail` - Assert compilation fails
- `Then the AST should contain a mixin declaration "X"` - Check AST
- `Then the mixin should have N fields` - Validate field count
- `Then field "X" should have type "Y"` - Validate field types
- `Then the error should mention "X"` - Validate error messages
- And many more...

## Example Scenario

```gherkin
Scenario: Declare a simple mixin with fields
  Given a file "timestamp.smp" with content:
    """
    mixin Timestamp:
        var created_at: i64
        var updated_at: i64
    """
  When I parse the file
  Then parsing should succeed
  And the AST should contain a mixin declaration "Timestamp"
  And the mixin should have 2 fields
  And field "created_at" should have type "i64"
```

## Adding New Tests

### 1. Add Scenario to Feature File
Edit `specs/features/mixin_*.feature`:
```gherkin
Scenario: Your new test
  Given ...
  When ...
  Then ...
```

### 2. Implement Missing Steps (if any)
Add to `main.rs`:
```rust
#[then(regex = r"^your new assertion$")]
async fn your_new_step(world: &mut MixinWorld) {
    // Implementation
}
```

### 3. Run Tests
```bash
cargo test --test bdd_mixins
```

## Current Status

- ✅ Test infrastructure set up
- ✅ 25+ step definitions implemented
- ✅ 26 scenarios defined
- ⏳ Build in progress
- 🚧 Full test execution pending

## Dependencies

```toml
[dev-dependencies]
cucumber = "0.21"
tokio = { version = "1", features = ["macros", "rt-multi-thread"] }
```

## TODO

- [ ] Implement full AST inspection (replace TODO markers)
- [ ] Add HIR compilation steps
- [ ] Add type checker integration
- [ ] Add property-based test generation
- [ ] Add performance benchmarks

## References

- Cucumber Rust: https://github.com/cucumber-rs/cucumber
- Gherkin Syntax: https://cucumber.io/docs/gherkin/
- Feature Specs: `../../specs/features/mixin_*.feature`
- Completion Plan: `../../doc/plans/mixin_completion_plan_2026_01_08.md`
