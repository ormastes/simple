# Spec Framework - Matchers Reference

Complete reference of available matchers in the Simple BDD Spec Framework.

## Contents

1. [Equality & Identity](#equality--identity)
2. [Comparison](#comparison)
3. [Collections](#collection-matchers)
4. [Strings](#string-matchers)
5. [Errors](#error-matchers)
6. [Negation](#negation)
7. [Custom Matchers](#custom-matchers)

---

## Equality & Identity

### eq - Equality

```simple
expect value to eq expected
expect 42 to eq 42
expect "hello" to eq "hello"
```

### be - Identity/Equality

```simple
expect value to be expected
expect 5 to be 5
expect "test" to be "test"
```

### be_nil - Nil Check

```simple
expect value to be_nil
let x: Any = nil
expect x to be_nil
```

---

## Comparison

### gt - Greater Than

```simple
expect value to gt other
expect 10 to gt 5      # pass
expect 5 to gt 10      # fail
```

### lt - Less Than

```simple
expect value to lt other
expect 5 to lt 10      # pass
expect 10 to lt 5      # fail
```

### gte - Greater Than or Equal

```simple
expect value to gte other
expect 10 to gte 10    # pass
expect 10 to gte 5     # pass
expect 5 to gte 10     # fail
```

### lte - Less Than or Equal

```simple
expect value to lte other
expect 5 to lte 5      # pass
expect 5 to lte 10     # pass
expect 10 to lte 5     # fail
```

---

## Collection Matchers

### include - Contains Element

```simple
expect collection to include value
expect [1, 2, 3] to include 2
expect [1, 2, 3] to include 5      # fail
expect "hello" to include "l"      # strings work too
```

### have_length / have_size - Collection Length

```simple
expect collection to have_length size
expect [1, 2, 3] to have_length 3
expect [1, 2, 3] to have_size 3    # alias
expect [] to have_length 0
expect "hello" to have_length 5
```

### be_empty - Empty Collection

```simple
expect collection to be_empty
expect [] to be_empty
expect {} to be_empty
expect "" to be_empty
expect [1] to be_empty             # fail
```

---

## String Matchers

### include_string - Contains Substring

```simple
expect string to include_string substring
expect "hello world" to include_string "world"
expect "hello world" to include_string "xyz"   # fail
```

### start_with - String Prefix

```simple
expect string to start_with prefix
expect "hello world" to start_with "hello"
expect "hello" to start_with "bye"             # fail
```

### end_with - String Suffix

```simple
expect string to end_with suffix
expect "hello world" to end_with "world"
expect "hello" to end_with "bye"               # fail
```

### be_blank - Blank/Empty String

```simple
expect string to be_blank
expect "" to be_blank
expect "   " to be_blank
expect "\n\t" to be_blank
expect "hello" to be_blank                     # fail
```

---

## Error Matchers

### expect_raises - Exception Handling

With specific error type:
```simple
expect_raises ErrorType:
    risky_operation()

expect_raises ValueError:
    raise ValueError("invalid")
```

Any error:
```simple
expect_raises:
    operation_that_might_fail()

expect_raises:
    1 / 0
```

---

## Negation

Use `not_to` to negate any matcher:

```simple
expect value not_to eq expected
expect 5 not_to eq 6
expect [1, 2, 3] not_to include 5
expect "hello" not_to start_with "bye"
expect [1] not_to be_empty
```

---

## Direct Assertions

Direct comparisons without matchers:

```simple
expect 5 == 5
expect "hello" != "world"
expect 10 > 5
expect true                        # truthiness check
```

---

## Syntax Summary

```simple
expect actual to matcher expected
expect actual not_to matcher expected
```

Examples:
```simple
# Equality
expect 42 to eq 42
expect name to eq "Alice"

# Comparison
expect score to gt 100
expect items to lte 10

# Collections
expect list to have_length 5
expect dict to include "key"
expect data to be_empty

# Strings
expect message to start_with "Error"
expect path to end_with ".spl"
expect input to be_blank

# Negation
expect result not_to be_nil
expect values not_to include 0
```

---

## Common Patterns

### Testing Collections

```simple
context "collection tests":
    given_lazy :items, \:
        [1, 2, 3, 4, 5]

    it "has items":
        expect items to have_length 5

    it "includes value":
        expect items to include 3

    it "not empty":
        expect items not_to be_empty
```

### Testing Strings

```simple
context "string tests":
    given_lazy :message, \:
        "Error: Invalid input"

    it "starts correctly":
        expect message to start_with "Error"

    it "includes text":
        expect message to include_string "Invalid"

    it "ends with input":
        expect message to end_with "input"
```

### Testing Exceptions

```simple
context "error handling":
    it "raises on invalid input":
        expect_raises ValueError:
            validate_required("")

    it "raises any error":
        expect_raises:
            dangerous_operation()
```

---

## Custom Matchers

Extend with custom matchers by implementing the Matcher trait:

```simple
class BeDivisibleByMatcher:
    divisor: Int

impl Matcher[Int] for BeDivisibleByMatcher:
    fn match(self, actual: Int) -> MatchResult:
        if actual % self.divisor == 0:
            return MatchResult.success()
        else:
            return MatchResult.failure(
                "Expected ${actual} to be divisible by ${self.divisor}"
            )

fn be_divisible_by(divisor: Int) -> BeDivisibleByMatcher:
    return BeDivisibleByMatcher { divisor: divisor }

# Usage
expect 12 to be_divisible_by 3     # pass
expect 13 to be_divisible_by 3     # fail
```

---

## Matcher Summary

| Category | Matchers |
|----------|----------|
| Equality | eq, be, be_nil |
| Comparison | gt, lt, gte, lte |
| Collections | include, have_length, have_size, be_empty |
| Strings | include_string, start_with, end_with, be_blank |
| Errors | expect_raises |

All matchers support negation with `not_to`.

---

## See Also

- [Spec Framework Guide](spec_framework_guide.md)
- [BDD Specification](bdd_spec.md)
