# Spec Framework - Matchers Reference

Complete reference of available matchers in the Simple BDD Spec Framework.

## Equality & Identity

### `eq` - Equality
```simple
expect value to eq expected
expect 42 to eq 42           # ✓
expect "hello" to eq "hello" # ✓
```

### `be` - Identity/Equality
```simple
expect value to be expected
expect 5 to be 5              # ✓
expect "test" to be "test"    # ✓
```

### `be_nil` - Nil Check
```simple
expect value to be_nil
let x: Any = nil
expect x to be_nil            # ✓
```

## Comparison

### `gt` - Greater Than
```simple
expect value to gt other
expect 10 to gt 5             # ✓
expect 5 to gt 10             # ✗
```

### `lt` - Less Than
```simple
expect value to lt other
expect 5 to lt 10             # ✓
expect 10 to lt 5             # ✗
```

### `gte` - Greater Than or Equal
```simple
expect value to gte other
expect 10 to gte 10           # ✓
expect 10 to gte 5            # ✓
expect 5 to gte 10            # ✗
```

### `lte` - Less Than or Equal
```simple
expect value to lte other
expect 5 to lte 5             # ✓
expect 5 to lte 10            # ✓
expect 10 to lte 5            # ✗
```

## Collection Matchers

### `include` - Contains Element
Check if collection includes a value:
```simple
expect collection to include value
expect [1, 2, 3] to include 2        # ✓
expect [1, 2, 3] to include 5        # ✗
expect "hello" to include "l"        # String works too
```

### `have_length` / `have_size` - Collection Length
Check exact collection length:
```simple
expect collection to have_length size
expect [1, 2, 3] to have_length 3    # ✓
expect [1, 2, 3] to have_size 3      # ✓ (alias)
expect [] to have_length 0           # ✓
expect "hello" to have_length 5      # ✓
```

### `be_empty` - Empty Collection
Check if collection is empty:
```simple
expect collection to be_empty
expect [] to be_empty                # ✓
expect {} to be_empty                # ✓
expect "" to be_empty                # ✓
expect [1] to be_empty               # ✗
```

## String Matchers

### `include_string` - Contains Substring
```simple
expect string to include_string substring
expect "hello world" to include_string "world"     # ✓
expect "hello world" to include_string "hello"     # ✓
expect "hello world" to include_string "xyz"       # ✗
```

### `start_with` - String Prefix
Check if string starts with prefix:
```simple
expect string to start_with prefix
expect "hello world" to start_with "hello"         # ✓
expect "test" to start_with "te"                   # ✓
expect "hello" to start_with "bye"                 # ✗
```

### `end_with` - String Suffix
Check if string ends with suffix:
```simple
expect string to end_with suffix
expect "hello world" to end_with "world"           # ✓
expect "test" to end_with "st"                     # ✓
expect "hello" to end_with "bye"                   # ✗
```

### `be_blank` - Blank/Empty String
Check if string is empty or whitespace only:
```simple
expect string to be_blank
expect "" to be_blank                              # ✓
expect "   " to be_blank                           # ✓
expect "\n\t" to be_blank                          # ✓
expect "hello" to be_blank                         # ✗
```

## Error Matchers

### `raise_error` / `expect_raises` - Exception Handling
Check if code raises an exception:
```simple
expect_raises ErrorType:
    risky_operation()

expect_raises:
    operation_that_might_fail()
```

Example:
```simple
expect_raises ValueError:
    raise ValueError("invalid value")

expect_raises:
    1 / 0  # ZeroDivisionError
```

## Negation

Use `not_to` to negate any matcher:
```simple
expect value not_to eq expected
expect 5 not_to eq 6                     # ✓
expect [1, 2, 3] not_to include 5        # ✓
expect "hello" not_to start_with "bye"   # ✓
expect [] not_to be_empty                # ✗
```

## Direct Assertions

You can also use direct comparisons without matchers:
```simple
expect 5 == 5                            # ✓
expect "hello" != "world"                # ✓
expect 10 > 5                            # ✓
expect true                              # Check truthiness
```

## Matcher Syntax

All matchers follow the same pattern:

```simple
expect actual to matcher expected
expect actual not_to matcher expected
```

### Examples
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

## Common Patterns

### Testing Collection Content
```simple
context "collection tests":
    given_lazy :items, \:
        [1, 2, 3, 4, 5]

    it "has items":
        expect items to have_length 5

    it "includes specific value":
        expect items to include 3

    it "not empty":
        expect items not_to be_empty
```

### Testing String Content
```simple
context "string tests":
    given_lazy :message, \:
        "Error: Invalid input"

    it "has message":
        expect message to have_length 21

    it "starts correctly":
        expect message to start_with "Error"

    it "includes text":
        expect message to include_string "Invalid"

    it "ends with input":
        expect message to end_with "input"
```

### Testing with Negation
```simple
context "negative assertions":
    it "value is not nil":
        let result = calculate()
        expect result not_to be_nil

    it "list doesn't include value":
        expect [1, 2, 3] not_to include 5

    it "string is not blank":
        let name = "Alice"
        expect name not_to be_blank
```

### Testing Exceptions
```simple
context "error handling":
    it "raises on invalid input":
        expect_raises ValueError:
            validate_required("")

    it "raises specific error":
        expect_raises:
            dangerous_operation()
```

## Matcher Composition

Matchers work with expressions:
```simple
expect calculate() to eq 42
expect user.name to start_with "A"
expect database.query() to have_length 0
```

Chain matchers with logical operators:
```simple
expect (x > 5) and (x < 10)             # Both conditions
expect value to be 42 and value != 43   # Multiple assertions
```

## Custom Matchers

You can extend with custom matchers by implementing the Matcher trait:
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
expect 12 to be_divisible_by 3        # ✓
expect 13 to be_divisible_by 3        # ✗
```

## Matcher Availability

| Category | Matchers |
|----------|----------|
| **Equality** | eq, be, be_nil |
| **Comparison** | gt, lt, gte, lte |
| **Collections** | include, have_length, have_size, be_empty |
| **Strings** | include_string, start_with, end_with, be_blank |
| **Errors** | raise_error, expect_raises |

All matchers support negation with `not_to`.

## See Also

- [Spec Framework Guide](doc/spec_framework_guide.md)
- [BDD Specification](doc/spec/bdd_spec.md)
- [Context Sharing Guide](doc/context_sharing_usage_guide.md)
