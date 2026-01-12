# Generic Syntax Deprecation Plan: `[]` → `<>`

**Date**: 2026-01-12
**Status**: Implementation Guide
**Related**: `type_parameter_syntax_analysis.md`, `unified_wrapper_unwrap_proposal.md`

---

## Summary

Deprecate square bracket syntax `[]` for generic/template types in favor of angle brackets `<>` to align with industry standards and improve visual clarity.

---

## Current State

The parser in `/home/ormastes/dev/pub/simple/src/parser/src/parser_types.rs` (lines 204-287) **already supports both syntaxes**:

```rust
// Line 205-206
let using_angle_brackets = self.check(&TokenKind::Lt);
let using_square_brackets = self.check(&TokenKind::LBracket);
```

Both are accepted without warnings.

---

## Implementation Plan

### Phase 1: Add Deprecation Warning

**File**: `src/parser/src/parser_types.rs`
**Location**: After line 208

```rust
if using_angle_brackets || using_square_brackets {
    // NEW: Emit deprecation warning for []
    if using_square_brackets {
        use crate::error_recovery::{ErrorHint, ErrorHintLevel};
        let warning = ErrorHint {
            level: ErrorHintLevel::Warning,
            message: format!(
                "Deprecated syntax for type parameters: use angle brackets <> instead of []\n\
                 Suggestion: {}< ... > instead of {}[ ... ]",
                name, name
            ),
            span: self.previous.span,
        };
        self.error_hints.push(warning);
    }

    self.advance(); // consume '[' or '<'
    // ... rest of parsing ...
}
```

### Phase 2: Update Error Messages

Add helper text to guide users:

```rust
fn suggest_generic_syntax_fix(type_name: &str, span: Span) -> String {
    format!(
        "help: use angle brackets for generic types\n\
         note: {}[T] is deprecated, use {}<T> instead\n\
         note: run `simple migrate --fix-generics` to auto-migrate",
        type_name, type_name
    )
}
```

### Phase 3: Create Migration Tool

**New CLI command**: `simple migrate --fix-generics <path>`

#### Algorithm:

1. Parse each `.spl` file
2. Identify generic type uses with `[]`
3. Replace `TypeName[Args]` with `TypeName<Args>`
4. Handle nested generics: `List[Dict[K, V]]` → `List<Dict<K, V>>`
5. Preserve array syntax: `[T]` (array type) stays as-is
6. Preserve array indexing: `arr[0]` stays as-is

#### Example Implementation:

```rust
// In src/driver/src/cli/migrate.rs (new file)
use regex::Regex;

pub fn migrate_generic_syntax(source: &str) -> String {
    let mut result = source.to_string();

    // Pattern: Identifier followed by [ then type content then ]
    // But NOT: [ at start of line (array type) or after = (array literal)
    let re = Regex::new(
        r"(?P<ident>[A-Z][a-zA-Z0-9_]*)\[(?P<args>[^]]+)\]"
    ).unwrap();

    result = re.replace_all(&result, |caps: &regex::Captures| {
        let ident = &caps["ident"];
        let args = &caps["args"];

        // Skip if this looks like it's in a value context
        // (Would need more sophisticated parsing)

        format!("{}<{}>", ident, args)
    }).to_string();

    result
}
```

### Phase 4: Update Stdlib

```bash
# Run migration tool on stdlib
cd simple/std_lib
simple migrate --fix-generics src/
```

Expected changes:
- `Option[T]` → `Option<T>`
- `Result[T, E]` → `Result<T, E>`
- `List[T]` → `List<T>`
- `Dict[K, V]` → `Dict<K, V>`
- `Gpu[T]` → `Gpu<T>`
- etc.

### Phase 5: Update Documentation

Files to update:
- All `.md` files in `doc/`
- All examples in `simple/std_lib/test/features/`
- Tutorial files
- API documentation

```bash
# Find all docs with [] generic syntax
grep -r '\[T\]' doc/ simple/std_lib/ --include="*.md" --include="*.spl"
```

### Phase 6: Deprecation Timeline

| Phase | Duration | Action |
|-------|----------|--------|
| **0.x.x** | 2 weeks | Add warning, announce migration |
| **0.x+1.x** | 1 month | Migrate stdlib, update docs |
| **0.x+2.x** | 2 months | Community migration period |
| **1.0.0** | - | Remove `[]` support (breaking change) |

---

## Compiler Warning Format

### Example Warning Output

```
warning: deprecated syntax for type parameters
  --> src/main.spl:12:15
   |
12 | let x: List[Int] = [1, 2, 3]
   |            ^^^^^ use angle brackets instead: List<Int>
   |
   = note: square bracket syntax for type parameters is deprecated
   = help: run `simple migrate --fix-generics` to auto-fix
```

### Warning Severity Levels

1. **Warning** (default): Non-blocking, shows in compiler output
2. **Error** (with `--deny-deprecated`): Treats deprecation as error
3. **Allow** (with `--allow-deprecated`): Suppresses warnings

---

## Edge Cases to Handle

### 1. Array Types vs Generic Types

```simple
# Array type (KEEP [])
type IntArray = [i32]
type FixedArray = [i32; 10]

# Generic type (CHANGE to <>)
type IntList = List<i32>     # Was: List[i32]
```

**Detection**: `[` at start of type expression = array type

### 2. Array Indexing vs Type Parameters

```simple
# Array indexing (KEEP [])
let elem = arr[0]
let item = matrix[i][j]

# Type parameters (CHANGE to <>)
let list: List<String> = []   # Was: List[String]
```

**Detection**: `[` after identifier in type position = generic

### 3. SIMD Vectors

```simple
# SIMD syntax uses [] (KEEP)
type Vec4 = vec[4, f32]

# But generic containers use <>
type VecList = List<vec[4, f32]>   # Was: List[vec[4, f32]]
```

### 4. Nested Generics

```simple
# Before
Dict[String, List[Option[User]]]

# After
Dict<String, List<Option<User>>>

# Migration must be careful with nesting depth
```

### 5. Constructor Type

```simple
# Before
Constructor[Widget, (i32, String)]

# After
Constructor<Widget, (i32, String)>
```

---

## Testing Plan

### Unit Tests

```rust
// In src/parser/tests/types.rs

#[test]
fn test_deprecated_bracket_generic() {
    let source = "let x: Option[Int]";
    let mut parser = Parser::new(source);
    let _result = parser.parse();

    // Should have one warning
    assert_eq!(parser.error_hints.len(), 1);
    assert!(matches!(
        parser.error_hints[0].level,
        ErrorHintLevel::Warning
    ));
}

#[test]
fn test_angle_bracket_generic_no_warning() {
    let source = "let x: Option<Int>";
    let mut parser = Parser::new(source);
    let _result = parser.parse();

    // Should have no warnings
    assert_eq!(parser.error_hints.len(), 0);
}

#[test]
fn test_array_type_no_warning() {
    let source = "let x: [Int]";  // Array type
    let mut parser = Parser::new(source);
    let _result = parser.parse();

    // Should have no warnings (this is array syntax)
    assert_eq!(parser.error_hints.len(), 0);
}
```

### Integration Tests

```simple
# test/deprecation/generic_brackets_spec.spl

Feature: Generic Type Syntax Deprecation
  Background:
    Deprecated [] syntax should emit warnings
    New <> syntax should work without warnings

  Scenario: Using deprecated bracket syntax
    Given source: "let x: List[Int] = []"
    When parsed
    Then warning emitted: "use angle brackets instead"
    And compiles successfully

  Scenario: Using new angle bracket syntax
    Given source: "let x: List<Int> = []"
    When parsed
    Then no warnings
    And compiles successfully

  Scenario: Array types still work
    Given source: "let x: [Int] = [1, 2, 3]"
    When parsed
    Then no warnings
    And compiles successfully
```

---

## Migration Examples

### Before & After

```simple
# ============ BEFORE ============
struct Container[T]:
    value: T

fn map[T, U](list: List[T], f: fn(T) -> U) -> List[U]:
    ...

let nums: List[Int] = [1, 2, 3]
let opt: Option[String] = Some("hello")
let result: Result[Data, Error] = Ok(data)
let gpu: Gpu[Tensor, GpuIndex::Gpu0] = compute()

# ============ AFTER ============
struct Container<T>:
    value: T

fn map<T, U>(list: List<T>, f: fn(T) -> U) -> List<U>:
    ...

let nums: List<Int> = [1, 2, 3]  # Array literal unchanged
let opt: Option<String> = Some("hello")
let result: Result<Data, Error> = Ok(data)
let gpu: Gpu<Tensor, GpuIndex::Gpu0> = compute()
```

---

## Rollback Plan

If migration causes significant issues:

1. **Revert warning addition**: Remove deprecation warning code
2. **Keep dual syntax**: Continue supporting both indefinitely
3. **Document both**: Show both syntaxes in docs with preference note

---

## Community Communication

### Announcement Template

```markdown
# [RFC] Migrating Generic Syntax from [] to <>

## Summary
We're deprecating `List[T]` in favor of `List<T>` to align with industry standards.

## Motivation
- Industry standard (Rust, C++, Java, TypeScript all use <>)
- Clear visual separation from array indexing
- Reduces confusion for new users

## Migration Path
1. Compiler warnings added in v0.x.x
2. Auto-migration tool: `simple migrate --fix-generics`
3. 3-month grace period
4. Breaking change in v1.0.0

## Your Action Required
Run `simple migrate --fix-generics .` in your project root

## Questions?
Reply to this RFC or open an issue
```

---

## Implementation Checklist

- [ ] Add deprecation warning to parser (Phase 1)
- [ ] Update error messages with helpful suggestions
- [ ] Create `simple migrate --fix-generics` tool
- [ ] Test migration tool on stdlib
- [ ] Migrate stdlib code
- [ ] Update all documentation
- [ ] Write migration guide
- [ ] Announce to community
- [ ] Monitor community feedback
- [ ] Address migration issues
- [ ] Plan 1.0.0 breaking change removal

---

## Conclusion

This is a **breaking change** done carefully with:
- ✅ Long deprecation period
- ✅ Automated migration tool
- ✅ Clear warnings and documentation
- ✅ Gradual rollout

**Estimated effort**: 2-3 weeks for full implementation and migration

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-12
**Status**: Implementation guide ready for review
