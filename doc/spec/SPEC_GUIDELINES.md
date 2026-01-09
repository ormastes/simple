# Specification File Guidelines

**Last Updated:** 2026-01-09  
**Purpose:** Guide for writing executable specification files in tests/*_spec.spl format

---

## Overview

Specification files (`*_spec.spl`) are executable specifications that combine:
1. **Documentation** - Comprehensive spec text in docstrings
2. **Test cases** - Executable examples that validate the spec
3. **Feature mapping** - Explicit Feature ID linkage

This creates a single source of truth where specs ARE tests and tests ARE specs.

---

## File Structure

### Basic Template

```simple
"""
# [Feature Name] Specification

**Status:** [Stable|Draft|Implementing|Planned]
**Feature IDs:** #XXX-YYY
**Keywords:** keyword1, keyword2, keyword3
**Topics:** topic1, topic2
**Migrated From:** doc/spec/[original].md (if migrated)

## Overview

Brief description of the feature and its purpose.

## Design Rationale

Why this feature exists and design decisions made.

## Specification

Detailed specification text, including:
- Syntax rules
- Semantic behavior
- Edge cases
- Examples

## Related Specifications

- **[Related Spec]** - How it relates to this spec
"""

# Test cases validating the specification

## Test: [Section Name]

"""
### Scenario: [Brief description]

Detailed test scenario explanation from the specification.
Can include multiple paragraphs and examples.
"""

test "descriptive_test_name":
    """
    Additional test-specific documentation.
    """
    # Test code here
    assert_compiles()

test "another_test":
    let x = example()
    assert x == expected
```

---

## Docstring Format

### Header Section (Required)

```simple
"""
# Feature Name Specification

**Status:** Stable
**Feature IDs:** #20-29
**Keywords:** types, mutability, generics
**Topics:** type-system
"""
```

**Status Values:**
- `Stable` - Complete spec + implementation
- `Implementing` - Complete spec, partial implementation  
- `Draft` - Spec under development
- `Planned` - Not yet started
- `Deprecated` - Superseded

**Feature IDs:** Cross-reference to feature catalog (e.g., `#20-29`, `#13`)

**Keywords:** Search terms for finding related specs (comma-separated)

**Topics:** High-level categories (use topic tags from doc/spec/README.md)

### Overview Section (Required)

Brief 2-4 sentence description of what the feature does.

```simple
## Overview

[Feature] provides [capability] through [mechanism].
It supports [key features] and is designed for [use cases].
```

### Specification Section (Required)

Detailed specification text. Include:

1. **Syntax** - How to write the feature
2. **Semantics** - What it means/does
3. **Rules** - Constraints and validation
4. **Examples** - Usage examples
5. **Edge Cases** - Special situations

Use markdown formatting within docstrings:
- Code blocks: ` ```simple ... ``` `
- Lists: `- item` or `1. item`
- Emphasis: `**bold**`, `*italic*`
- Links: `[text](file.md)` (for reference only)

### Related Specifications (Optional)

```simple
## Related Specifications

- **[Spec Name]** - Brief description of relationship
- **[Another Spec]** - How they interact
```

---

## Test Cases

### Test Structure

Each test should:
1. Have a descriptive name (use snake_case)
2. Include a scenario docstring explaining what's being tested
3. Contain executable code that validates the spec
4. Use appropriate assertions

```simple
## Test: Feature Section Name

"""
### Scenario: What this tests

Explanation of the test scenario, what behavior is validated,
and any relevant context from the specification.
"""

test "feature_behavior_case":
    """
    Specific details about this test case.
    """
    # Arrange
    let input = setup()
    
    # Act
    let result = feature_function(input)
    
    # Assert
    assert result == expected_value
```

### Test Categories

**1. Syntax Tests** - Verify code compiles:
```simple
test "syntax_valid":
    let x: i64 = 42
    assert_compiles()
```

**2. Behavior Tests** - Verify runtime behavior:
```simple
test "behavior_correct":
    let result = compute(10)
    assert result == 20
```

**3. Error Tests** - Verify errors are caught:
```simple
test "error_detected":
    # This should fail type checking
    let x: str = 42
    assert_compile_error("type mismatch")
```

**4. Edge Case Tests** - Test boundaries:
```simple
test "edge_case_max_int":
    let max = 9223372036854775807  # i64::MAX
    let overflow = max + 1
    assert overflow == -9223372036854775808
```

### Test Naming Conventions

Use descriptive snake_case names that explain what's being tested:

✅ **Good:**
- `basic_type_annotation`
- `mutable_struct_field_update`
- `async_function_returns_promise`
- `error_missing_required_capability`

❌ **Bad:**
- `test1`, `test2`
- `it_works`
- `check_stuff`

### Test Documentation

Each test should have a docstring explaining:
1. **What** is being tested
2. **Why** it matters (if not obvious)
3. **How** it validates the spec

```simple
test "type_inference_from_literal":
    """
    Test that integer literals infer to i64 type by default.
    
    This validates the specification section "Literal Type Rules"
    which states that bare integer literals like 42 should infer
    as i64 unless context demands otherwise.
    """
    let x = 42
    assert typeof(x) == "i64"
```

---

## Comment-Only Specifications

If a feature is purely conceptual or has no testable implementation yet,
you can create a comment-only _spec.spl file:

```simple
"""
# Future Feature Specification

**Status:** Planned
**Feature IDs:** #XXX-YYY

## Overview

This feature is planned but not yet implemented.

## Specification

[Full specification text here]
"""

# No test cases yet - spec only
```

**Note:** Comment-only files compile successfully. You can add tests later
as implementation progresses.

---

## Migration from Markdown

When migrating from doc/spec/*.md:

1. **Preserve metadata** - Status, Feature IDs, Keywords
2. **Extract overview** - First few paragraphs
3. **Convert examples** - Code blocks become tests
4. **Keep context** - Explanatory text becomes test docstrings
5. **Add "Migrated From" metadata** - Reference original file

Use the migration script:
```bash
python scripts/migrate_spec_to_spl.py doc/spec/types.md tests/specs/types_spec.spl
```

---

## File Organization

```
tests/
├── specs/                      # Feature specifications
│   ├── syntax_spec.spl         # Core language features
│   ├── types_spec.spl
│   ├── functions_spec.spl
│   ├── async_default_spec.spl
│   └── ...
│
├── system/                     # Integration tests
│   ├── mixin_spec.spl          # Complex feature interactions
│   ├── static_polymorphism_spec.spl
│   └── ...
│
└── meta/                       # Meta tests
    └── comment_only_spec.spl   # Tool/compiler tests
```

**Naming Convention:** `[feature_name]_spec.spl`

---

## Best Practices

### 1. Single Responsibility
Each _spec.spl file should cover one cohesive feature or system.

✅ **Good:** `types_spec.spl` covers type system  
❌ **Bad:** `everything_spec.spl` covers all features

### 2. Comprehensive Documentation
Docstrings should be detailed enough that someone could implement
the feature from the spec alone.

### 3. Executable Examples
Every example in the spec should be runnable as a test (when possible).

### 4. Progressive Disclosure
Start with simple examples, progress to complex cases:

```simple
# 1. Basic usage
test "basic": ...

# 2. Common patterns  
test "common_pattern": ...

# 3. Edge cases
test "edge_case_boundary": ...

# 4. Error handling
test "error_invalid_input": ...
```

### 5. Keep Specs Updated
When implementation changes, update the spec immediately.
The spec should always reflect current behavior.

### 6. Cross-Reference Related Specs
Use "Related Specifications" section to link related features.

---

## Assertions Available

```simple
# Compilation checks
assert_compiles()                    # Code should compile
assert_compile_error("msg")          # Should fail with message

# Value assertions
assert expr                          # Boolean must be true
assert x == y                        # Equality
assert x != y                        # Inequality
assert x > y, x >= y, x < y, x <= y  # Comparisons

# Type assertions
assert typeof(x) == "i64"            # Type checking
assert is_instance(x, MyClass)       # Instance check

# Collection assertions
assert len(list) == 5                # Length
assert item in collection            # Membership
```

---

## Generating Documentation

Convert _spec.spl back to markdown:

```bash
# Generate all specs
simple spec-gen --all

# Generate specific spec
simple spec-gen --input tests/specs/types_spec.spl \
                --output doc/spec/generated/types.md
```

Generated markdown will include:
- Extracted docstring content
- Test case summaries
- Feature ID cross-references
- "Generated from" notice

---

## Examples

### Example 1: Simple Feature Spec

See: `tests/meta/comment_only_spec.spl`

### Example 2: Comprehensive Feature Spec

See: `tests/system/mixin_spec.spl`

### Example 3: Integration Test

See: `tests/system/static_polymorphism_spec.spl`

---

## Checklist for New Specs

When creating a new _spec.spl file:

- [ ] Header with Status, Feature IDs, Keywords, Topics
- [ ] Overview section (2-4 sentences)
- [ ] Comprehensive specification text
- [ ] Related Specifications section (if applicable)
- [ ] At least 3-5 test cases covering:
  - [ ] Basic usage
  - [ ] Common patterns
  - [ ] Edge cases
  - [ ] Error cases (if applicable)
- [ ] Descriptive test names
- [ ] Test docstrings explaining scenarios
- [ ] File compiles without errors
- [ ] All tests pass (or marked as TODO)

---

## See Also

- [Migration Plan](../SPEC_MIGRATION_PLAN.md) - Full migration strategy
- [Migration Status](MIGRATION_STATUS.md) - Current progress
- [AGENTS.md](../../AGENTS.md) - Development guidelines
- [Feature Index](../features/feature.md) - Feature catalog

---

**Questions?** See [CLAUDE.md](../../CLAUDE.md) or existing _spec.spl examples.
