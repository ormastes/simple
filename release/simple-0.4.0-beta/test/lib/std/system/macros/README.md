# Macro System Test Suite

Comprehensive system tests for the Simple language macro system (#1300-#1324).

## Test Files

### 1. `macro_system_spec.spl` - Basic Macro System
Tests fundamental macro functionality:

**Basic macro expansion**
- Simple expression macros
- Macros with const parameters
- Multiple macro invocations

**Hygienic expansion**
- Variable capture prevention
- Unique name generation
- Scope isolation

**Template substitution**
- Templates in identifiers
- Templates in strings
- Templates in function names (f-strings)

**Const-eval engine**
- Arithmetic evaluation
- Conditional evaluation
- Loop evaluation

### 2. `macro_contracts_spec.spl` - Contract System
Tests the contract-first macro system:

**intro contracts**
- Function introduction to modules
- Multiple function generation with const-eval loops
- Class method introduction
- Template substitution in intro declarations

**inject contracts**
- Statement injection at function entry
- Multiple injection points (entry/exit)
- Cross-cutting concerns

**returns contracts**
- Simple value returns
- Computed values from const-eval
- Function reference returns

**Combined contracts**
- intro + returns
- Macro chaining
- Complex compositions

### 3. `macro_advanced_spec.spl` - Advanced Features
Tests advanced macro capabilities:

**DSL support**
- Custom infix operators
- Domain-specific notation
- Fluent APIs

**Nested macros**
- Nested invocations
- Macro chaining
- Macros in macro definitions

**Integration with language features**
- Pattern matching
- Async/await
- Generics
- Traits

**Macro composition**
- Multiple macro coordination
- Boilerplate generation
- Builder patterns

### 4. `macro_errors_spec.spl` - Error Handling
Tests error detection and edge cases:

**Contract validation**
- Missing emit blocks (E1401)
- Type mismatches (E1402)
- Invalid intro targets (E1403)

**Template substitution errors**
- Undefined variables (E1404)
- Type errors in const-eval (E1405)

**Edge cases**
- Empty macro bodies
- Const-eval only macros
- Long loops
- Deep nesting
- Many parameters
- Special characters
- Numeric templates

**Hygiene edge cases**
- Shadowing
- Multiple bindings
- Recursive generation

**Const-eval edge cases**
- String operations
- Nested conditionals
- Nested loops
- Early returns

### 5. `macro_integration_spec.spl` - Cross-Feature Integration
Tests macros working with other language features:

**Cross-module usage**
- Importing macros
- Macro composition across scopes

**Decorators**
- Applying decorators to generated functions
- Multiple decorator combinations

**Pattern matching**
- Generating pattern matching code
- Destructuring in expansions

**Async/await**
- Generating async functions
- Actor spawning

**Traits**
- Implementing traits via macros
- Generating trait methods

**Generics**
- Generic class generation
- Generic function generation

**Comprehensions**
- List comprehensions in macros
- Dict comprehensions

**Real-world patterns**
- Builder pattern
- Serialization
- Validation

## Running Tests

### Run all macro tests
```bash
cargo test -p simple-driver simple_stdlib_system_macros
```

### Run specific test files
```bash
# Basic system tests
cargo test -p simple-driver simple_stdlib_system_macros_macro_system_spec

# Contract tests
cargo test -p simple-driver simple_stdlib_system_macros_macro_contracts_spec

# Advanced features
cargo test -p simple-driver simple_stdlib_system_macros_macro_advanced_spec

# Error handling
cargo test -p simple-driver simple_stdlib_system_macros_macro_errors_spec
```

### Run integration tests
```bash
cargo test -p simple-driver simple_stdlib_integration_macros_macro_integration_spec
```

### Run with interpreter directly
```bash
./target/debug/simple simple/std_lib/test/system/macros/macro_system_spec.spl
./target/debug/simple simple/std_lib/test/system/macros/macro_contracts_spec.spl
./target/debug/simple simple/std_lib/test/system/macros/macro_advanced_spec.spl
./target/debug/simple simple/std_lib/test/system/macros/macro_errors_spec.spl
./target/debug/simple simple/std_lib/test/integration/macros/macro_integration_spec.spl
```

## Test Coverage

### Features Tested

| Feature ID | Feature | Test Coverage |
|------------|---------|---------------|
| #1300 | `macro` keyword with contract syntax | ✅ All test files |
| #1301 | `const_eval:` and `emit:` blocks | ✅ macro_system_spec.spl |
| #1302 | Hygienic macro expansion | ✅ macro_system_spec.spl, macro_errors_spec.spl |
| #1303 | `intro`/`inject`/`returns` contracts | ✅ macro_contracts_spec.spl |
| #1304 | One-pass LL(1) macro compilation | ✅ macro_system_spec.spl, macro_contracts_spec.spl |
| #1305-#1307 | DSL Support | ✅ macro_advanced_spec.spl |
| #1308-#1311 | Built-in Decorators | ✅ macro_integration_spec.spl |
| #1312-#1313 | Comprehensions | ✅ macro_integration_spec.spl |
| #1314-#1319 | Pattern Matching | ✅ macro_integration_spec.spl |
| #1320-#1324 | Slicing & Spread | ✅ (Tested separately in pattern tests) |

### Test Statistics

- **Total test files:** 5 (4 system + 1 integration)
- **Total test contexts:** ~40
- **Total test cases:** ~100+
- **Feature coverage:** 25/25 features (100%)

### Error Code Coverage

| Error Code | Description | Test File |
|------------|-------------|-----------|
| E1401 | Missing emit block | macro_errors_spec.spl |
| E1402 | Contract type mismatch | macro_errors_spec.spl |
| E1403 | Invalid intro target | macro_errors_spec.spl |
| E1404 | Undefined template variable | macro_errors_spec.spl |
| E1405 | Type error in const-eval | macro_errors_spec.spl |

## Test Patterns

### Testing Template Substitution
```simple
macro make_fn(name: Str const) -> ():
    emit code:
        fn "{name}"() -> Str:
            return "{name} value"

make_fn!("test")
expect(test()).to_eq("test value")
```

### Testing Hygiene
```simple
let x = 100

macro shadow() -> (returns result: Int):
    emit result:
        let x = 50  # Should not affect outer x
        x

expect(shadow!()).to_eq(50)
expect(x).to_eq(100)  # Outer x unchanged
```

### Testing Const-Eval
```simple
macro sum(n: Int const) -> (returns total: Int):
    const_eval:
        let sum = 0
        for i in 0..n:
            sum = sum + i
    emit total:
        {sum}

expect(sum!(5)).to_eq(10)  # 0+1+2+3+4
```

### Testing Intro Contracts
```simple
macro make_getter(field: Str const) -> (
    intro getter:
        enclosing.module.fn "get_{field}"() -> Str
):
    emit getter:
        fn "get_{field}"() -> Str:
            return "{field} value"

make_getter!("name")
expect(get_name()).to_eq("name value")
```

## Test Organization

```
simple/std_lib/test/
├── system/macros/
│   ├── README.md                    # This file
│   ├── macro_system_spec.spl        # Basic functionality
│   ├── macro_contracts_spec.spl     # Contract system
│   ├── macro_advanced_spec.spl      # Advanced features
│   └── macro_errors_spec.spl        # Error handling
└── integration/macros/
    └── macro_integration_spec.spl   # Cross-feature integration
```

## Maintenance

### Adding New Tests

1. **Choose the right file:**
   - Basic functionality → `macro_system_spec.spl`
   - Contract features → `macro_contracts_spec.spl`
   - Advanced/DSL features → `macro_advanced_spec.spl`
   - Error cases → `macro_errors_spec.spl`
   - Cross-feature → `macro_integration_spec.spl`

2. **Follow BDD structure:**
   ```simple
   describe "Feature Area":
       context "Specific scenario":
           it "does something specific":
               # Test code
               expect(result).to_eq(expected)
   ```

3. **Test both success and failure:**
   - Positive test: verify expected behavior
   - Negative test: verify error detection (in errors_spec.spl)
   - Edge cases: boundary conditions, empty inputs, large inputs

4. **Keep tests focused:**
   - One concept per test
   - Clear test names
   - Minimal setup

### Common Issues

**Problem:** Test fails with "undefined variable"
- **Solution:** Check hygiene - macro-generated names are unique

**Problem:** Template not substituting
- **Solution:** Verify const parameter type matches usage

**Problem:** Const-eval error
- **Solution:** Ensure all variables in const-eval block are compile-time constants

## Related Documentation

- `doc/spec/macro.md` - Macro specification
- `doc/spec/metaprogramming.md` - Metaprogramming features
- `doc/contracts/macro_contracts.md` - Contract processing details
- `doc/report/METAPROGRAMMING_COMPLETE_2025-12-27.md` - Implementation report
- `simple/examples/test_macro_*.spl` - Example macro usage

## Status

**Last Updated:** 2025-12-27
**Test Status:** ✅ All passing
**Coverage:** 100% of macro features (25/25)
**Maintainer:** Simple Language Team
