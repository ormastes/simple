# Naming Convention Mutability Research

Research on using naming conventions to indicate variable mutability instead of keywords.

## Goal

Design a system where variable mutability is determined by naming convention rather than explicit keywords (`val`/`var`), while avoiding conflicts with type names.

---

## Current System (Keywords)

```simple
val counter = Counter(value: 0)    # Immutable
var counter = Counter(value: 0)    # Mutable
```

## Proposed System (Naming Convention)

| Convention | Mutability | Rebindable | Functional Update (`->`) |
|------------|-----------|------------|--------------------------|
| `Name` (Capital) | Immutable | No | No |
| `name` (lowercase) | Immutable | No | Yes (creates new) |
| `name_` (underscore suffix) | Mutable | Yes | Yes |

---

## Key Features

### 1. Underscore Suffix = Mutable

```simple
counter_ = 0
counter_ = counter_ + 1    # OK - mutable, can reassign
counter_ += 1              # OK - can mutate
```

### 2. Capital Letter = Immutable, Non-Rebindable

```simple
Counter = Counter(value: 0)
Counter = Counter(value: 1)    # ERROR - cannot rebind
Counter->increment()           # ERROR - cannot use -> on non-rebindable
```

### 3. Lowercase = Immutable, Supports Functional Update

```simple
counter = Counter(value: 0)
counter = counter + 1          # ERROR - cannot reassign directly
counter->increment()           # OK - functional update creates new instance
```

### 4. Private Members (Underscore Prefix)

```simple
pub struct Counter:
    _value: i32    # Private field (underscore prefix)
    count: i32     # Public field
```

---

## The Naming Conflict Problem

### Type Names vs Variable Names

Both type names and "non-rebindable immutable" variables start with capital letters:

```simple
Counter = Counter(value: 0)
#   ^         ^
#   |         |
#   Variable? Type name
#
# CONFLICT: Parser cannot distinguish!
```

### Examples of Conflict

```simple
# Is this a type annotation or variable assignment?
Point = Point(x: 0, y: 0)

# Is this calling a constructor or referencing a variable?
val p = Point
```

---

## Solution Options

### Option A: Different Sigil for Non-Rebindable

Use a special prefix for non-rebindable variables:

```simple
$counter = Counter(value: 0)   # $ = non-rebindable
counter = Counter(value: 0)    # lowercase = immutable with ->
counter_ = Counter(value: 0)   # underscore = mutable
```

**Pros:**
- Clear distinction from type names
- Single character prefix

**Cons:**
- New sigil to learn
- Less readable

### Option B: Remove Capital Variable Convention

Only use underscore suffix for mutability:

```simple
counter = Counter(value: 0)    # Immutable, supports ->
counter_ = Counter(value: 0)   # Mutable
```

No capital letter variables - capitals reserved for types only.

**Pros:**
- Simple rule: underscore = mutable
- No conflict with type names
- Consistent with other languages

**Cons:**
- Loses "non-rebindable" feature
- All immutable vars support `->` (maybe not desired)

### Option C: Contextual Parsing

Parser uses context to distinguish:

```simple
# Assignment context: variable
counter = Counter(value: 0)

# Type context: type
fn foo() -> Counter:
```

For capital names:
- Left of `=` without type annotation = variable
- After `->` in function signature = type
- After `:` in type annotation = type

```simple
# Variable (capital, left of =)
MyCounter = Counter(value: 0)

# Type (after ->)
fn get() -> Counter:

# Type (after :)
val x: Counter = Counter(value: 0)
```

**Pros:**
- Keeps all features
- Natural reading

**Cons:**
- Complex parsing rules
- Potential ambiguity

### Option D: Mandatory Type Annotation for Capital Variables

Capital variables require explicit type annotation to disambiguate:

```simple
# With type annotation - clearly a variable
MyCounter: Counter = Counter(value: 0)

# Without annotation - treated as type reference/error
Counter = Counter(value: 0)   # ERROR: Cannot assign to type
```

**Pros:**
- Clear disambiguation
- Self-documenting code

**Cons:**
- More verbose
- Breaking the "no keyword" goal

### Option E: Use ALL_CAPS for Non-Rebindable

Reserve SCREAMING_CASE for non-rebindable constants:

```simple
COUNTER = Counter(value: 0)    # Non-rebindable (ALL_CAPS)
counter = Counter(value: 0)    # Immutable with ->
counter_ = Counter(value: 0)   # Mutable
Counter                        # Always a type name
```

**Pros:**
- Common convention in many languages
- Clear visual distinction
- No conflict with PascalCase types

**Cons:**
- ALL_CAPS typically used for constants, not variables
- Less elegant for non-constant values

---

## Language Comparison

### Scala

```scala
val x = 5      // Immutable
var x = 5      // Mutable
// No naming convention for mutability
```

### Haskell

```haskell
-- All variables immutable by default
-- Naming doesn't affect mutability
x = 5
```

### Ruby

```ruby
CONSTANT = 5   # Constant (ALL_CAPS)
variable = 5   # Mutable
@instance = 5  # Instance variable
@@class = 5    # Class variable
```

### Go

```go
const X = 5    // Constant (any case)
var x = 5      // Mutable
// Uppercase = exported, not mutability
```

### Erlang

```erlang
% Variables start with uppercase, all immutable
X = 5
% Atoms start with lowercase
atom
```

Note: Erlang's convention is opposite - capitals for variables, lowercase for atoms!

---

## Detailed Analysis

### Erlang-Inspired Approach

Erlang uses capital letters for variables and lowercase for atoms/constants. We could invert this:

```simple
# Erlang-inspired (inverted)
counter = immutable_value    # Lowercase = immutable
Counter = TYPE_NAME          # Capital = type (not variable)
COUNTER = constant           # ALL_CAPS = compile-time constant
counter_ = mutable_value     # Underscore suffix = mutable
```

### Recommended Solution: Option B + E Hybrid

Combine the simplest approaches:

```simple
# Types (PascalCase)
Counter, Point, MyClass

# Constants (ALL_CAPS) - compile-time, non-rebindable
MAX_SIZE = 100
PI = 3.14159

# Immutable variables (lowercase) - supports ->
counter = Counter(value: 0)
counter->increment()         # Creates new Counter

# Mutable variables (underscore suffix)
counter_ = 0
counter_ += 1                # Direct mutation
```

---

## Functional Update Operator (`->`)

### For Immutable Variables (lowercase)

```simple
counter = Counter(value: 0)

# Method call rebinding
counter->increment()
# Desugars to: counter = counter.increment()

# Field update rebinding
counter->value = counter.value + 1
# Desugars to: counter = Counter(value: counter.value + 1, ...other_fields)
```

### For Mutable Variables (underscore suffix)

```simple
counter_ = Counter(value: 0)

# Can use -> or direct mutation
counter_->increment()        # Functional style
counter_.value += 1          # Direct mutation (if field is mut)
counter_ = counter_ + 1      # Direct reassignment
```

### For Constants (ALL_CAPS)

```simple
COUNTER = Counter(value: 0)

# Cannot use -> or reassign
COUNTER->increment()         # ERROR
COUNTER = other              # ERROR
```

---

## Implicit `self` Return

Methods returning `self` type have implicit return:

```simple
impl Counter:
    # Return type specifies 'self' (or Counter)
    fn increment() -> self:
        self->value = self.value + 1
        # Implicit return of new self
```

The `self` keyword as return type means:
- Returns the same type as the implementing struct
- Implicit return of `self` at end of method
- Enables fluent/builder pattern

---

## Summary Table

| Name Pattern | Category | Rebindable | `->` Update | Direct Mutate |
|--------------|----------|-----------|-------------|---------------|
| `CONSTANT` | Constant | No | No | No |
| `TypeName` | Type | N/A | N/A | N/A |
| `variable` | Immutable | No | Yes | No |
| `variable_` | Mutable | Yes | Yes | Yes |
| `_private` | Private field | Depends | Depends | Depends |

---

## Recommendation

**Adopt Option B + E Hybrid:**

1. **ALL_CAPS** for compile-time constants (non-rebindable)
2. **PascalCase** reserved for type names only
3. **lowercase** for immutable variables (support `->`)
4. **lowercase_** (underscore suffix) for mutable variables
5. **_underscore** (underscore prefix) for private members

This provides:
- No conflict between types and variables
- Clear visual distinction for mutability
- Familiar conventions from other languages
- Clean, keyword-free syntax

---

## Open Questions

1. Should `->` work on mutable variables too, or only immutable?
2. How to handle constants that need complex initialization?
3. Should private members (`_name`) inherit mutability from the suffix?
   - `_name` = private immutable?
   - `_name_` = private mutable?
4. How does this interact with method parameters?

---

## References

- [Erlang Variables](https://www.erlang.org/doc/reference_manual/expressions.html)
- [Ruby Constants](https://ruby-doc.org/docs/ruby-doc-bundle/UsersGuide/rg/constants.html)
- [Scala val/var](https://docs.scala-lang.org/overviews/scala-book/two-types-variables.html)
- Simple Language: `doc/research/implicit_self_grammar.md`
