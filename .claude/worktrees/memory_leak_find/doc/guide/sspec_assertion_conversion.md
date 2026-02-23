# SSpec Assertion Conversion Guide

**Purpose:** Convert manual if/else assertions to SSpec expect() syntax
**Context:** Required after running `simple migrate --fix-sspec-docstrings`
**Time:** ~2-5 minutes per assertion

---

## Quick Reference

| Pattern | Before | After |
|---------|--------|-------|
| Equality | `if x == y:` | `expect(x).to(eq(y))` |
| Inequality | `if x != y:` | `expect(x).to_not(eq(y))` |
| Greater | `if x > y:` | `expect(x).to(be_greater_than(y))` |
| Less | `if x < y:` | `expect(x).to(be_less_than(y))` |
| Boolean true | `if flag:` | `expect(flag).to(be_true())` |
| Boolean false | `if !flag:` | `expect(flag).to(be_false())` |
| Contains | `if list.contains(x):` | `expect(list).to(contain(x))` |
| Member | `if obj.field:` | `expect(obj).to(have_member("field"))` |

---

## Problem: Empty If/Else Blocks

After migration, you'll see this pattern:

```simple
val result = compute_something()
if result == expected:
else:
```

**Parse Error:**
```
error: parse error: Unexpected token: expected Indent, found Else
```

**Why?** The migration tool removed:
- `print('[PASS] message')`
- `passed = passed + 1`
- `print('[FAIL] message')`
- `failed = failed + 1`

Leaving empty blocks that are syntactically invalid.

---

## Solution: Convert to expect() Assertions

### Step 1: Identify the Assertion Pattern

Look at the if condition:
```simple
if result == expected:
else:
```

### Step 2: Convert to expect() Syntax

```simple
expect(result).to(eq(expected))
```

### Step 3: Remove Empty Blocks

Delete the entire if/else structure.

---

## Conversion Examples

### Example 1: Simple Equality

**Before (after migration):**
```simple
val hook = create_hook("before_each", 1)
if hook.hook_type == "before_each":
else:
```

**After (manual fix):**
```simple
val hook = create_hook("before_each", 1)
expect(hook.hook_type).to(eq("before_each"))
```

---

### Example 2: Multiple Conditions (AND)

**Before:**
```simple
if hooks[0].order == 1 and hooks[2].order == 3:
else:
```

**After:**
```simple
expect(hooks[0].order).to(eq(1))
expect(hooks[2].order).to(eq(3))
```

**Alternative (composite):**
```simple
expect(hooks[0].order == 1 and hooks[2].order == 3).to(be_true())
```

---

### Example 3: Numeric Comparison

**Before:**
```simple
if value > 0:
else:
```

**After:**
```simple
expect(value).to(be_greater_than(0))
```

---

### Example 4: Range Check

**Before:**
```simple
if x >= 10 and x <= 20:
else:
```

**After:**
```simple
expect(x).to(be_in_range(10, 20))
```

**Alternative (separate):**
```simple
expect(x).to(be_greater_than_or_equal(10))
expect(x).to(be_less_than_or_equal(20))
```

---

### Example 5: Type Checking

**Before:**
```simple
if result.is_ok():
else:
```

**After:**
```simple
expect(result).to(be_ok())
```

---

### Example 6: Collection Contains

**Before:**
```simple
if items.contains("test"):
else:
```

**After:**
```simple
expect(items).to(contain("test"))
```

---

### Example 7: String Operations

**Before:**
```simple
if text.starts_with("prefix"):
else:
```

**After:**
```simple
expect(text).to(start_with("prefix"))
```

---

### Example 8: Null/None Checks

**Before:**
```simple
if value != nil:
else:
```

**After:**
```simple
expect(value).to_not(be_nil())
```

**Alternative:**
```simple
expect(value).to(be_some())  # if using Option<T>
```

---

## Available Matchers

### Equality Matchers
- `eq(expected)` - Equal to
- `not_eq(expected)` - Not equal to

### Numeric Matchers
- `be_greater_than(n)` - Greater than
- `be_less_than(n)` - Less than
- `be_greater_than_or_equal(n)` - ≥
- `be_less_than_or_equal(n)` - ≤
- `be_in_range(min, max)` - Between (inclusive)

### Boolean Matchers
- `be_true()` - Is true
- `be_false()` - Is false

### Type Matchers
- `be_ok()` - Result is Ok
- `be_err()` - Result is Err
- `be_some()` - Option is Some
- `be_none()` - Option is None
- `be_nil()` - Value is nil

### Collection Matchers
- `contain(item)` - Collection contains item
- `have_length(n)` - Collection has size n
- `be_empty()` - Collection is empty

### String Matchers
- `start_with(prefix)` - String starts with
- `end_with(suffix)` - String ends with
- `match_pattern(regex)` - Matches regex

### Object Matchers
- `have_member(name)` - Object has field/method
- `be_instance_of(type)` - Is instance of type

---

## Negation

Use `to_not()` instead of `to()` for negation:

```simple
expect(value).to_not(eq(0))
expect(list).to_not(be_empty())
expect(result).to_not(be_err())
```

---

## Complex Assertions

### Multiple Assertions on Same Value

**Pattern:**
```simple
val user = get_user()
expect(user.name).to(eq("Alice"))
expect(user.age).to(be_greater_than(18))
expect(user.email).to(contain("@"))
```

### Nested Expectations

**Pattern:**
```simple
val result = compute()
expect(result).to(be_ok())
expect(result.unwrap()).to(eq(42))
```

**Better:**
```simple
val result = compute()
expect(result).to(be_ok())
val value = result.unwrap()
expect(value).to(eq(42))
```

### Error Messages

**Add custom messages:**
```simple
expect(config.timeout).to(eq(30), "Timeout should default to 30 seconds")
```

---

## Batch Conversion Strategy

### Step 1: Search for Empty Blocks

```bash
grep -n "^if.*:$" file_spec.spl | grep -A 1 "else:"
```

### Step 2: Group by Pattern

- Equality checks (most common)
- Range checks
- Type checks
- Collection operations

### Step 3: Convert in Order

1. Simple equality (fastest)
2. Numeric comparisons
3. Boolean checks
4. Complex multi-condition assertions

### Step 4: Verify Syntax

```bash
simple file_spec.spl
```

Check for parse errors, fix, repeat.

---

## Common Mistakes

### ❌ Mistake 1: Forgetting to Remove If/Else

**Wrong:**
```simple
if result == expected:
    expect(result).to(eq(expected))
else:
```

**Right:**
```simple
expect(result).to(eq(expected))
```

### ❌ Mistake 2: Incorrect Matcher

**Wrong:**
```simple
expect(value > 0).to(be_true())  # Works but not idiomatic
```

**Right:**
```simple
expect(value).to(be_greater_than(0))  # Clearer intent
```

### ❌ Mistake 3: Missing Unwrap

**Wrong:**
```simple
val result = Result<i32, text> = get_result()
expect(result).to(eq(42))  # Type mismatch!
```

**Right:**
```simple
val result = get_result()
expect(result).to(be_ok())
expect(result.unwrap()).to(eq(42))
```

---

## Testing Your Conversions

### Quick Verification

```bash
# Parse check
simple before_each_spec.spl

# Run tests
simple test before_each_spec.spl

# Check output
# All assertions should pass or fail with clear messages
```

### Assertion Quality Checklist

- [ ] All if/else blocks removed
- [ ] Each assertion has clear intent
- [ ] Proper matchers used (not all `eq()`)
- [ ] Negations use `to_not()` not `eq(false)`
- [ ] Complex conditions split into multiple expects
- [ ] Custom error messages added where helpful

---

## Time Estimates

| Assertion Type | Time per Assertion |
|----------------|-------------------|
| Simple equality | 30 seconds |
| Numeric comparison | 1 minute |
| Boolean check | 1 minute |
| Collection operation | 2 minutes |
| Complex multi-condition | 3-5 minutes |

**Average file (20 assertions):** 30-60 minutes

---

## Example: Complete File Conversion

### Before Migration (Original)

```simple
print('describe User validation:')
print('  it validates email format:')

var passed = 0
var failed = 0

val email = "user@example.com"
if email.contains("@"):
    print('      [PASS] email has @ symbol')
    passed = passed + 1
else:
    print('      [FAIL] email missing @')
    failed = failed + 1

print("Total: {passed} passed, {failed} failed")
```

### After Migration (Automated)

```simple
describe "User validation":
    """
    TODO: Add documentation here
    """
    it "validates email format":
        """
        TODO: Add documentation here
        """

val email = "user@example.com"
if email.contains("@"):
else:
```

### After Manual Conversion (Final)

```simple
describe "User validation":
    """
    ## User Validation

    Tests for user input validation including email format,
    password strength, and username requirements.
    """
    it "validates email format":
        """
        Given a valid email address
        When validating the format
        Then the email should contain @ symbol

        Example:
        ```simple
        validate_email("user@example.com") # ✓ valid
        validate_email("invalid.email")     # ✗ invalid
        ```
        """
        val email = "user@example.com"
        expect(email).to(contain("@"))
        expect(email).to(match_pattern(r"\w+@\w+\.\w+"))
```

---

## Next Steps

After converting assertions:

1. **Fill in docstrings** - Replace TODO with comprehensive documentation
2. **Run tests** - Verify all assertions pass
3. **Review output** - Check for clear failure messages
4. **Commit changes** - Document what was migrated

---

## Reference

- **SSpec Documentation:** `doc/spec/testing/testing_bdd_framework.md`
- **Matcher Reference:** `simple/std_lib/src/spec/matchers.spl`
- **Migration Tool:** `simple migrate --fix-sspec-docstrings`
- **Conversion Example:** `doc/examples/sspec_conversion_example.md`

---

**End of Guide**
