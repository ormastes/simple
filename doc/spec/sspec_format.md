# SSpec Format - Specification-based Testing

## Overview

SSpec (Specification Test) is Simple's integrated testing and documentation format. It combines:
- **Executable tests** written in Simple syntax
- **Markdown documentation** embedded as triple-quoted strings
- **Specification generation** that produces human-readable docs

## File Naming Convention

```
*_spec.spl
```

Examples:
- `mixin_spec.spl`
- `static_polymorphism_spec.spl`
- `type_inference_spec.spl`

## Format Structure

### 1. Module Documentation

Start the file with a module-level doc comment:

```simple
"""
# Feature Name Specification

## Overview
High-level description of the feature.

## Syntax
```simple
# Code examples
```

## Key Concepts
- Concept 1
- Concept 2
"""
```

### 2. Test Sections

Organize tests into logical sections:

```simple
## Test: Feature Name

"""
### Scenario: Specific scenario description

Detailed explanation of what this test validates.
Can include code examples, expected behavior, edge cases.
"""

# Actual test code
test "test name":
    let result = some_function()
    assert result == expected_value
```

### 3. Helper Code

Include helper types, functions, and test utilities:

```simple
## Helper Types and Functions

struct Helper:
    field: Type

fn helper_function() -> Result:
    # implementation
```

## Documentation Comments

### Triple-Quote Format

Use `"""` for multi-line markdown comments:

```simple
"""
# Heading

Regular markdown content including:
- Lists
- Code blocks with ```simple
- Tables
- Links

## Subsections
More content...
"""
```

### Inline vs Block Comments

```simple
# Single-line comment (not included in generated docs)

"""
Multi-line documentation comment
Included in generated specification
"""
```

## Test Assertions

SSpec tests use assertion functions:

```simple
test "test name":
    # Positive assertions
    assert condition
    assert value == expected
    assert_compiles()
    
    # Negative assertions
    assert_fails()
    assert_fails_with("error message substring")
```

## Generated Documentation

### Output Location

Generated docs go to:
```
doc/spec/
  ├── mixin_spec.md
  ├── static_polymorphism_spec.md
  └── ...
```

### Generation Process

1. Parser extracts `"""` documentation blocks
2. Test structure is converted to specification format
3. Markdown is generated with:
   - Feature overview from module doc
   - Test scenarios with code examples
   - Implementation notes
   - Cross-references

### Example Generated Output

From this SSpec:
```simple
"""
# Feature X
## Overview
Feature description
"""

## Test: Basic Usage
"""
### Scenario: Simple case
Validates basic behavior
"""
test "basic test":
    assert true
```

Generates:
````markdown
# Feature X

## Overview
Feature description

## Test Scenarios

### Scenario: Simple case
Validates basic behavior

**Test Code:**
```simple
test "basic test":
    assert true
```

**Status:** ✅ Pass
````

## Advantages Over Cucumber

| Aspect | Cucumber (.feature) | SSpec (.spl) |
|--------|---------------------|--------------|
| Language | Gherkin DSL | Native Simple |
| Type checking | No | Yes |
| IDE support | Limited | Full Simple tooling |
| Code reuse | Separate step definitions | Direct code |
| Documentation | Separate | Integrated |
| Maintenance | Two codebases | Single source |

## Integration with Lean Verification

SSpec tests can reference formal verification:

```simple
"""
### Lean Verification

This feature is verified in:
- `verification/TypeInference.lean` - Soundness proof
- `verification/MixinSubstitution.lean` - Type safety

**Properties Verified:**
1. Type substitution preserves well-typedness
2. Mixin application is associative
3. No field conflicts lead to type errors
"""
```

The build system can check that:
- Referenced Lean files exist
- Lean proofs successfully verify
- Test behavior matches proven properties

## Best Practices

### 1. One Feature Per File

Each `*_spec.spl` focuses on a single language feature:
- `mixin_spec.spl` - Mixin feature
- `trait_spec.spl` - Trait system
- `async_spec.spl` - Async/await

### 2. Progressive Complexity

Order tests from simple to complex:
```simple
## Test: Basic Case
## Test: With Generics
## Test: Edge Cases
## Test: Error Handling
```

### 3. Comprehensive Scenarios

Cover:
- Happy path (success cases)
- Edge cases (boundary conditions)
- Error cases (expected failures)
- Performance considerations
- Integration with other features

### 4. Clear Documentation

Each test section should explain:
- **What** is being tested
- **Why** it matters
- **How** it works
- **Edge cases** to consider

### 5. Helper Organization

Place helpers at the end:
```simple
## Test: Feature 1
## Test: Feature 2
## ...
## Helper Types and Functions
```

## Running SSpec Tests

### Compile and Run

```bash
# Run all sspec tests
make test-sspec

# Run specific spec file
simple test tests/system/mixin_spec.spl

# Generate documentation
simple spec-doc tests/system/mixin_spec.spl
```

### Test Output

```
mixin_spec.spl:
  ✅ Basic Mixin Declaration
  ✅ Mixin with Methods
  ✅ Generic Mixin
  ⏭️  Mixin Field Conflict Detection (skipped)
  ❌ Required Methods (failed)
     Expected: compilation success
     Got: type error at line 234
```

## Migration from Cucumber

To migrate `.feature` files to SSpec:

### 1. Convert Gherkin to Simple

Before (Cucumber):
```gherkin
Scenario: Declare a simple mixin
  Given a file "test.spl" with content:
    """
    mixin Timestamp:
        created_at: i64
    """
  When I parse the file
  Then parsing should succeed
```

After (SSpec):
```simple
"""
### Scenario: Declare a simple mixin
"""
mixin Timestamp:
    created_at: i64

test "simple mixin declaration":
    assert_compiles()
```

### 2. Inline Step Definitions

Cucumber steps become direct code:
```simple
# Instead of: Given the compiler is available
# Just use the compiler directly:

test "compile example":
    compile_and_check("test.spl")
```

### 3. Preserve Documentation

Move feature descriptions to module doc:
```simple
"""
# Feature Name
(content from Feature: description)
"""
```

Move scenario descriptions to test sections:
```simple
"""
### Scenario: Name
(content from Scenario: description)
"""
```

## Future Enhancements

### Planned Features

1. **Property-based testing**
   ```simple
   property "mixin composition is associative":
       forall m1, m2, m3 in mixins:
           assert (m1 + m2) + m3 == m1 + (m2 + m3)
   ```

2. **Performance benchmarks**
   ```simple
   benchmark "static dispatch":
       # Timing code
       assert time < max_time_ms
   ```

3. **Fuzzing support**
   ```simple
   fuzz "parser" with random_source_code:
       assert_no_crash()
   ```

4. **Literate programming**
   - Generate executable code from markdown
   - Embed SSpec in design documents

### Integration Opportunities

- **CI/CD**: Auto-generate spec docs on commit
- **IDE**: Show inline doc preview from SSpec
- **REPL**: Load spec file for interactive testing
- **Tutorial**: Generate beginner guides from specs

## References

- Implementation: `src/compiler/src/sspec/`
- Examples: `tests/system/*_spec.spl`
- Doc generator: `src/driver/src/spec_doc.rs`
- Lean integration: `verification/SSpecProps.lean`
