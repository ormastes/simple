# Existence Check `.?` Refactoring Patterns

**Last updated**: 2026-01-24
**Status**: Research / Refactoring Plan

## Overview

The `.?` existence check operator combined with no-paren method calls enables more concise code patterns that can replace verbose predicate methods like `is_some()`, `is_none()`, `is_ok()`, `is_err()`.

## Key Refactoring Patterns

### 1. Option Type Patterns

| Current | Refactored | Notes |
|---------|------------|-------|
| `opt.is_some()` | `opt.?` | Direct existence check |
| `opt.is_none()` | `not opt.?` | Negated existence check |
| `if opt.is_some(): use(opt!)` | `if opt.?: use(opt!)` | Guard pattern |

### 2. Result Type Patterns

| Current | Refactored | Notes |
|---------|------------|-------|
| `result.is_ok()` | `result.ok.?` | `ok()` returns `Option`, check with `.?` |
| `result.is_err()` | `result.err.?` | `err()` returns `Option`, check with `.?` |
| `not result.is_ok()` | `result.err.?` | More semantic |
| `not result.is_err()` | `result.ok.?` | More semantic |

### 3. Collection Patterns

| Current | Refactored | Notes |
|---------|------------|-------|
| `list.is_empty()` | `not list.?` | Empty = not present |
| `not list.is_empty()` | `list.?` | Has items = present |
| `str.is_empty()` | `not str.?` | Empty string = not present |
| `dict.is_empty()` | `not dict.?` | Empty dict = not present |

### 4. Chained Patterns

| Current | Refactored | Notes |
|---------|------------|-------|
| `list.first().is_some()` | `list.first.?` | No-paren + existence |
| `dict.get("key").is_some()` | `dict["key"].?` | Index + existence |
| `user.profile.is_some()` | `user.profile.?` | Field + existence |

## Method Availability

For the refactoring to work, the following methods must support no-paren calls:

### Result Methods (returning Option)
- `ok()` → `ok` - Returns `Some(value)` if Ok, `None` if Err
- `err()` → `err` - Returns `Some(error)` if Err, `None` if Ok

### Collection Methods (returning Option)
- `first()` → `first` - Returns first element or None
- `last()` → `last` - Returns last element or None
- `get(key)` → requires parens (has arg)

## Codebase Analysis

### Files with `is_ok()` / `is_err()` usage:

```
simple/std_lib/test/features/file_io_extended_spec.spl
  - 12 uses of is_ok()
  - 4 uses of is_err()

simple/std_lib/test/unit/testing/mock_verification_spec.spl
  - 8 uses of is_ok()
  - 6 uses of is_err()

simple/std_lib/test/unit/testing/contract_spec.spl
  - 2 uses of is_ok()

simple/std_lib/src/testing/mocking.spl
  - 1 use of is_ok()
  - 1 use of is_err()
```

### Files with `is_some()` / `is_none()` usage:

```
simple/std_lib/test/unit/testing/mock_phase6_spec.spl
  - 3 uses of is_some()
  - 2 uses of is_none()

simple/std_lib/test/unit/testing/mock_phase5_spec.spl
  - 1 use of is_some()
  - 1 use of is_none()

simple/std_lib/test/unit/testing/mock_phase4_spec.spl
  - 1 use of is_some()

simple/std_lib/test/unit/testing/mock_phase3_spec.spl
  - 1 use of is_some()
  - 5 uses of is_none()

simple/std_lib/test/unit/testing/mock_verification_spec.spl
  - 2 uses of is_some()

simple/std_lib/test/unit/testing/contract_spec.spl
  - 2 uses of is_some()

simple/std_lib/src/testing/mocking.spl
  - 1 use of is_some()
  - 2 uses of is_none()
```

## Refactoring Examples

### Before (verbose):
```simple
fn process_result(result: Result<i32, text>):
    if result.is_ok():
        val value = result.unwrap()
        print "Success: {value}"

    if result.is_err():
        val error = result.unwrap_err()
        print "Error: {error}"

fn check_option(opt: Option<User>):
    if opt.is_some():
        val user = opt.unwrap()
        print "User: {user.name}"

    if opt.is_none():
        print "No user found"
```

### After (concise with `.?`):
```simple
fn process_result(result: Result<i32, text>):
    if result.ok.?:
        val value = result!
        print "Success: {value}"

    if result.err.?:
        val error = result.unwrap_err()
        print "Error: {error}"

fn check_option(opt: Option<User>):
    if opt.?:
        val user = opt!
        print "User: {user.name}"

    if not opt.?:
        print "No user found"
```

### Chained Example:
```simple
# Before
if user.profile.is_some() and user.profile.unwrap().email.is_some():
    send_email(user.profile.unwrap().email.unwrap())

# After
if user?.profile.? and user!.profile!.email.?:
    send_email(user!.profile!.email!)

# Even better with guard
if user?.profile?.email.?:
    send_email(user!.profile!.email!)
```

## Refactoring Plan

### Phase 1: Ensure Method Support (Done)
- [x] `.?` existence operator implemented
- [x] No-paren method calls implemented
- [x] `ok()` and `err()` methods exist for Result

### Phase 2: Add Property Aliases (Optional)
Consider adding these as properties (not just methods):
- `Result.ok` → same as `ok()` but no-paren
- `Result.err` → same as `err()` but no-paren

These are already supported via no-paren method call fallback.

### Phase 3: Update Test Files (Low Priority)
Refactor test files to use new patterns:

| File | Changes |
|------|---------|
| `file_io_extended_spec.spl` | 16 patterns |
| `mock_verification_spec.spl` | 16 patterns |
| `mock_phase*.spl` | ~15 patterns |
| `contract_spec.spl` | 4 patterns |
| `mocking.spl` | 4 patterns |

**Total**: ~55 patterns can be refactored

### Phase 4: Documentation
- [ ] Update CLAUDE.md with new patterns
- [ ] Add examples to syntax_quick_reference.md
- [ ] Update feature documentation

## Comparison with Ruby

| Ruby | Simple (old) | Simple (new with .?) |
|------|--------------|---------------------|
| `x.nil?` | `x.is_none()` | `not x.?` |
| `!x.nil?` | `x.is_some()` | `x.?` |
| `x.present?` | `not x.is_empty()` | `x.?` |
| `x.blank?` | `x.is_empty()` | `not x.?` |
| `result.ok?` | `result.is_ok()` | `result.ok.?` |
| `result.err?` | `result.is_err()` | `result.err.?` |

## Benefits of Refactoring

1. **Shorter code**: `opt.?` vs `opt.is_some()`
2. **Consistent pattern**: Same `.?` for all existence checks
3. **Chainable**: `user?.profile?.email.?`
4. **Ruby-like feel**: Property-style access

## Risks and Considerations

1. **Learning curve**: Developers need to learn `.?` semantics
2. **Backwards compatibility**: Old patterns still work
3. **Readability**: Some may prefer explicit `is_some()` / `is_ok()`

## Recommendation

- **New code**: Use `.?` patterns
- **Existing code**: Refactor opportunistically during other changes
- **Tests**: Low priority, refactor when touching the file

## Summary Table

| Type | Check Present | Check Absent |
|------|---------------|--------------|
| Option | `opt.?` | `not opt.?` |
| Result (ok) | `result.ok.?` | `not result.ok.?` |
| Result (err) | `result.err.?` | `not result.err.?` |
| List | `list.?` | `not list.?` |
| Dict | `dict.?` | `not dict.?` |
| String | `str.?` | `not str.?` |
| Any value | `val.?` | `not val.?` |
