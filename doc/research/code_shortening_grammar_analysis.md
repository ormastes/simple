# Code Shortening Grammar Analysis

**Status:** Analysis & Recommendation
**Created:** 2026-01-06
**Purpose:** Evaluate high-leverage syntax features for adoption in Simple
**Topics:** syntax, grammar, ergonomics, LOC-reduction

This document analyzes "code shortening" grammars from mainstream languages and evaluates their applicability to Simple. These features compress common patterns (data construction, transformation, branching, error/null handling, binding, formatting) beyond just control flow.

---

## Contents

1. [Feature Status Matrix](#feature-status-matrix)
2. [Category A: Collection Construction](#category-a-collection-construction)
3. [Category B: Transformation Pipelines](#category-b-transformation-pipelines)
4. [Category C: Binding & Destructuring](#category-c-binding--destructuring)
5. [Category D: Null/Optional Safety](#category-d-nulloptional-safety)
6. [Category E: Error Propagation](#category-e-error-propagation)
7. [Category F: Function/Lambda Brevity](#category-f-functionlambda-brevity)
8. [Category G: String & Literal Ergonomics](#category-g-string--literal-ergonomics)
9. [Recommended Adoption Priority](#recommended-adoption-priority)
10. [Implementation Roadmap](#implementation-roadmap)

---

## Feature Status Matrix

| # | Feature | Status | Simple Support | Priority | Notes |
|---|---------|--------|----------------|----------|-------|
| **A. Collection Construction** |||||
| 1 | Comprehensions | ✅ **DONE** | `[x*2 for x in xs if pred(x)]` | - | Python-style |
| 2 | Spread in literals | ✅ **DONE** | `[*a, *b, 3]`, `{**d1, k: v}` | - | JS-style `*`/`**` |
| 3 | Range literals | ⚠️ **PARTIAL** | `0..n`, `0..<n` in patterns | MED | Need expression form |
| 4 | Slicing syntax | ⚠️ **PARTIAL** | Indexed access only | MED | Add `xs[a:b:c]` |
| **B. Transformation Pipelines** |||||
| 5 | Method chains | ✅ **DONE** | `xs.filter(p).map(f)` | - | Standard OOP |
| 6 | Pipeline operator | ❌ **MISSING** | No `\|>` | HIGH | High leverage |
| 7 | Placeholder argument | ❌ **MISSING** | Must use lambdas | HIGH | Combine with #6 |
| 8 | Fused filter+map | ❌ **MISSING** | Separate calls | LOW | Stdlib method |
| **C. Binding & Destructuring** |||||
| 9 | Destructuring | ✅ **DONE** | `let (a, b) = pair` | - | In let/patterns |
| 10 | Pattern matching | ✅ **DONE** | `match`/`case` with binding | - | Rust-style |
| 11 | Assignment expr | ❌ **MISSING** | No walrus `:=` | MED | Consider carefully |
| **D. Null/Optional Safety** |||||
| 12 | Optional chaining | ❌ **MISSING** | No `?.` | HIGH | Major ergonomics win |
| 13 | Nullish coalescing | ❌ **MISSING** | No `??`, `??=` | HIGH | Pairs with #12 |
| **E. Error Propagation** |||||
| 14 | Propagate operator | ❌ **MISSING** | No `?` postfix | HIGH | Huge LOC savings |
| **F. Function/Lambda Brevity** |||||
| 15 | Arrow lambdas | ✅ **DONE** | `\x: x * 2` | - | Backslash syntax |
| 16 | Expression-bodied fn | ❌ **MISSING** | Block required | MED | `fn f(x) => x * 2` |
| **G. String & Literal Ergonomics** |||||
| 17 | String interpolation | ✅ **DONE** | `"sum={a+b}"` | - | Default for `"..."` |
| 18 | Raw/multiline strings | ✅ **DONE** | `'...'`, `"""..."""` | - | Single/triple quotes |

**Legend:**
- ✅ **DONE** - Feature exists in Simple
- ⚠️ **PARTIAL** - Partial support, needs extension
- ❌ **MISSING** - Not yet implemented
- Priority: **HIGH** / **MED** / **LOW**

---

## Category A: Collection Construction

### 1. Comprehensions ✅ **DONE**

**Status:** Already implemented (Python-style)

**Simple Syntax:**
```simple
# List comprehension
let evens = [x * 2 for x in xs if x > 0]

# Dict comprehension
let mapping = {k: v * 2 for k, v in pairs if v > 0}

# Set comprehension (if sets exist)
let unique = {x for x in items}
```

**Grammar:**
```
list_comprehension: '[' expression repeat1(comprehension_clause) ']'
dict_comprehension: '{' expression ':' expression repeat1(comprehension_clause) '}'
comprehension_clause: 'for' pattern 'in' expression [guard]
```

**Analysis:**
- ✅ Python-style syntax (expr first, not LL(1) but familiar)
- ✅ Supports nested loops and guards
- ✅ Well-tested and documented

**Recommendation:** ✓ Keep as-is. Consider LL(1) form only if parser issues arise.

**LL(1) Alternative (not recommended):**
```simple
# Leading 'for' keyword makes it LL(1) unambiguous
let evens = [for x in xs if x > 0: x * 2]
```

---

### 2. Spread in Literals ✅ **DONE**

**Status:** Already implemented (JS-style with `*`/`**`)

**Simple Syntax:**
```simple
# Array spread
let combined = [1, 2, *xs, *ys, 99]

# Dict spread
let merged = {**defaults, **user_config, "override": true}
```

**Grammar:**
```
spread_element: '*' expression
dict_spread: '**' expression
```

**Analysis:**
- ✅ Uses `*` for arrays (like Python unpacking)
- ✅ Uses `**` for dicts (like Python `**kwargs`)
- ✅ LL(1)-friendly (prefix operator)
- ✅ Consistent with rest patterns (`*rest`)

**Recommendation:** ✓ Keep as-is. Well-designed and consistent.

---

### 3. Range Literals ⚠️ **PARTIAL**

**Current Status:** Range syntax exists in patterns but not as expressions

**Simple Current:**
```simple
# In patterns (match/case)
match x:
    case 0..10: ...      # Inclusive range
    case 0..<10: ...     # Exclusive range
```

**Missing:** Range expressions for iteration
```simple
# DESIRED: Range as expression
for i in 0..10:        # Should work
    print(i)

let range = 0..10      # Should create Range object
let arr = [0..10]      # Should expand to [0,1,2,...,10]
```

**Recommendation:** 🔧 **EXTEND**

**Implementation:**
1. Make `..` and `..<` binary operators that return `Range` objects
2. Add `Range` type to stdlib with iterator support
3. Grammar already parses ranges, just need runtime support

**Priority:** **MEDIUM** - Nice ergonomics but not critical

---

### 4. Slicing Syntax ⚠️ **PARTIAL**

**Current Status:** Only indexed access `xs[i]`

**Simple Current:**
```simple
let x = xs[0]          # Single element access
let x = xs[i]          # Index expression
```

**Missing:** Slice syntax
```simple
# DESIRED: Python-style slicing
let sub = xs[1:5]      # Elements 1 through 4
let sub = xs[:5]       # First 5 elements
let sub = xs[5:]       # From index 5 to end
let sub = xs[::2]      # Every 2nd element
let sub = xs[1:10:2]   # Start:stop:step
```

**Recommendation:** 🔧 **ADD**

**Grammar (Python-style):**
```
slice_expr: expression '[' [expression] ':' [expression] [':' [expression]] ']'
```

**Challenges:**
- Ambiguity with dict literal `{1:5}` vs slice `[1:5]`
  - Resolved by context: slices only in `[ ]` subscript, dicts only in `{ }` literal
- LL(1) parsing: Need lookahead after `[` to distinguish `xs[i]` vs `xs[i:j]`
  - Solution: Always parse index, check for `:` to convert to slice

**Priority:** **MEDIUM** - Very common in data processing

---

## Category B: Transformation Pipelines

### 5. Method Chains ✅ **DONE**

**Status:** Standard OOP method chaining

**Simple Syntax:**
```simple
let result = xs
    .filter(\x: x > 0)
    .map(\x: x * 2)
    .take(10)
    .to_list()
```

**Recommendation:** ✓ Keep as-is. Standard and working.

---

### 6. Pipeline Operator ❌ **MISSING**

**Status:** Not implemented

**Proposed Syntax:**
```simple
# Pipeline with lambda
let result = xs
    |> filter(\x: x > 0)
    |> map(\x: x * 2)
    |> sum()

# With placeholder (requires #7)
let result = xs
    |> filter(_ > 0)
    |> map(_ * 2)
    |> sum()

# Function composition
let process = parse |> validate |> transform |> save
```

**Benefits:**
- **Left-to-right dataflow** (more natural reading order)
- **Avoids deep nesting** of function calls
- **Pairs beautifully with placeholder syntax** (#7)
- **High leverage**: Transforms `f(g(h(x)))` to `x |> h |> g |> f`

**Grammar:**
```
pipeline_expr: expression ('|>' expression)+
```

**Implementation:**
```simple
# Desugaring
x |> f |> g
# Becomes
g(f(x))

# With placeholder
x |> f(_ + 1) |> g(_, y)
# Becomes
g(f(x + 1), y)
```

**Challenges:**
- **Precedence:** Should bind looser than most operators
- **Placeholder binding:** Need to determine `_` scope
- **Type inference:** Chain type must flow through

**Alternative Tokens:**
- `|>` - Elixir, F#, Elm (recommended)
- `->` - Conflicts with lambda return type
- `>>` - Conflicts with shift operator

**Recommendation:** 🎯 **HIGH PRIORITY ADD**

This is one of the **highest-leverage** features. Enables point-free style and dramatically improves readability of transformation chains.

**Example Impact:**
```simple
# Without pipeline (nested)
let result = sum(map(filter(xs, \x: x > 0), \x: x * 2))

# Without pipeline (intermediate vars)
let filtered = filter(xs, \x: x > 0)
let mapped = map(filtered, \x: x * 2)
let result = sum(mapped)

# With pipeline + placeholder
let result = xs |> filter(_ > 0) |> map(_ * 2) |> sum()
```

---

### 7. Placeholder Argument ❌ **MISSING**

**Status:** Not implemented (must use explicit lambdas)

**Proposed Syntax:**
```simple
# Current (verbose)
xs.map(\x: x * 2).filter(\x: x > 10)

# With placeholder
xs.map(_ * 2).filter(_ > 10)

# Multiple placeholders (positional)
pairs.map((_0, _1) -> _0 + _1)      # Option 1: numbered
pairs.map((a, b) -> a + b)           # Option 2: still use names for multi-arg

# In pipeline
data
    |> parse()
    |> validate(_ != nil)
    |> transform(_ * 2)
    |> save()
```

**Token Options:**
- `_` - Scala, Kotlin, Rust (recommended)
- `it` - Kotlin (when single arg)
- `$0`, `$1` - Swift (numbered)

**Benefits:**
- **Removes lambda ceremony** for 80% of cases
- **Pairs with pipeline** for maximum concision
- **Familiar from Rust, Kotlin, Scala**

**Grammar:**
```
placeholder: '_'
placeholder_lambda: expression containing '_'
```

**Semantic Rules:**
1. `_` creates implicit lambda in function arg position
2. Single `_` → `\x: <expr with _ replaced by x>`
3. Multiple uses of `_` → same parameter
4. Not allowed in arbitrary expressions (only function args)

**Implementation:**
```simple
# Desugaring
xs.map(_ * 2)
# Becomes
xs.map(\__placeholder: __placeholder * 2)

# Multiple uses
xs.map(_ * _ + 1)
# Becomes
xs.map(\x: x * x + 1)
```

**Challenges:**
- **Scope limitation**: Only works in arg position
  - `let f = _ * 2` - ERROR (not in arg position)
  - `xs.map(_ * 2)` - OK (arg to map)
- **Multi-arg functions**: Need syntax for multiple args
  - Option: Disallow `_` for multi-arg (force explicit lambda)
  - Option: `_0`, `_1` numbered placeholders

**Recommendation:** 🎯 **HIGH PRIORITY ADD**

**MUST** implement together with pipeline (#6) for maximum value.

**Suggested Rule:** Simple approach
- `_` only for **single-argument** functions
- For multi-arg, require explicit lambda: `\a, b: a + b`
- Keeps mental model simple

---

### 8. Fused filter+map ❌ **MISSING**

**Status:** Not implemented (separate filter/map calls)

**Proposed:**
```simple
# Current (two passes)
let results = xs
    .filter(\x: x.is_ok())
    .map(\x: x.unwrap())

# Fused (one pass)
let results = xs.filter_map(\x: x.ok())  # Returns Option, keeps Some values
```

**Analysis:**
- **LOW PRIORITY** - This is a stdlib method, not syntax
- Rust's `filter_map` is convenient but not essential
- Can be added to stdlib without language changes

**Recommendation:** 📚 **DEFER TO STDLIB**

Add as method on iterators/collections, not a language feature.

---

## Category C: Binding & Destructuring

### 9. Destructuring ✅ **DONE**

**Status:** Already implemented

**Simple Syntax:**
```simple
# Tuple destructuring
let (x, y) = point
let (a, b, *rest) = tuple

# Dict destructuring (if supported)
let {x, y} = point_obj
let {name, age} = user

# In function parameters
fn distance((x1, y1): Point, (x2, y2): Point) -> f64:
    return sqrt((x2-x1)^2 + (y2-y1)^2)

# In for loops
for (key, value) in dict:
    print("{key}: {value}")
```

**Recommendation:** ✓ Keep as-is. Well-designed.

---

### 10. Pattern Matching ✅ **DONE**

**Status:** Already implemented (Rust-style)

**Simple Syntax:**
```simple
match value:
    case [x, y]:
        print("Pair: {x}, {y}")
    case Point(x, y) if x > 0:
        print("Positive x")
    case _:
        print("Default")
```

**Recommendation:** ✓ Keep as-is. Excellent feature.

---

### 11. Assignment Expression ❌ **MISSING**

**Status:** Not implemented (no walrus operator `:=`)

**Python Example:**
```python
# Without walrus
m = re.match(pattern, string)
if m:
    use(m)

# With walrus
if (m := re.match(pattern, string)):
    use(m)
```

**Proposed Simple Syntax:**
```simple
# Option 1: Python-style :=
if (m := pattern.match(string)):
    use(m)

# Option 2: Regular = works in expression context
if (m = pattern.match(string)):
    use(m)

# Use case: loop with complex condition
while (line := file.read_line()) != nil:
    process(line)
```

**Benefits:**
- Reduces repetition of expensive calls
- Avoids pre-declaring variables
- Common in conditional + use patterns

**Risks:**
- **Easily abused** - can make code harder to read
- **Assignment vs equality** confusion if using `=`
- **Scoping questions** - lifetime of assigned variable?

**Recommendation:** ⚠️ **CONSIDER CAREFULLY**

**Decision needed:**
1. **Add with `:=`** (Python-style) - clear intent, new operator
2. **Add with `=`** - reuse existing operator, might be confusing
3. **Skip entirely** - force explicit pre-declaration

**Suggested approach:** Add `:=` with **linting rules**:
- Warn if used outside `if`/`while` conditions
- Warn if right-hand side is simple (no method call)
- Scope: Variable lives in if/while block only

**Priority:** **MEDIUM** - Useful but not critical, proceed with caution

---

## Category D: Null/Optional Safety

### 12. Optional Chaining ❌ **MISSING**

**Status:** Not implemented

**Current Verbose Approach:**
```simple
# Current: explicit checks
let name = if user != nil:
    if user.profile != nil:
        user.profile.name
    else:
        nil
else:
    nil

# Or with match
let name = match user:
    case Some(u):
        match u.profile:
            case Some(p): Some(p.name)
            case None: None
    case None: None
```

**Proposed Syntax:**
```simple
# Optional chaining
let name = user?.profile?.name  # Returns Option[String]

# Short-circuits to None if any part is None
user?.profile?.name  # If user is None → None
                      # If profile is None → None
                      # Otherwise → Some(name)
```

**Semantics:**
```simple
# Desugaring
user?.profile?.name

# Becomes
match user:
    case Some(u):
        match u.profile:
            case Some(p): Some(p.name)
            case None: None
    case None: None
```

**Grammar:**
```
optional_chain: expression ('?.' identifier)+
```

**Type Rules:**
- `expr?.field` where `expr: Option[T]` and `T` has `field: U` → result is `Option[U]`
- Chains automatically propagate `None`
- Works with methods: `user?.get_profile()?.name`

**Recommendation:** 🎯 **HIGH PRIORITY ADD**

This is a **major ergonomics win** for code using `Option` types.

**Impact Example:**
```simple
# Before (15 lines)
fn get_user_city(user_id: UserId) -> Option[String]:
    match find_user(user_id):
        case Some(user):
            match user.address:
                case Some(addr):
                    match addr.city:
                        case Some(city): return Some(city)
                        case None: return None
                case None: return None
        case None: return None

# After (3 lines)
fn get_user_city(user_id: UserId) -> Option[String]:
    find_user(user_id)?.address?.city
```

---

### 13. Nullish Coalescing ❌ **MISSING**

**Status:** Not implemented

**Proposed Syntax:**
```simple
# Nullish coalescing - provide default
let name = user?.name ?? "Anonymous"

# Nullish coalescing assignment
config.timeout ??= 100  # Set only if nil/None

# Works with Option types
let value: Option[i64] = get_value()
let result = value ?? 0  # Unwraps or provides default
```

**Operator:** `??`
- Different from `||` (logical or)
- Different from `?:` (ternary - conflicts with Optional type `T?`)

**Semantics:**
```simple
# Desugaring
a ?? b

# Becomes
match a:
    case Some(v): v
    case None: b

# Assignment form
x ??= y

# Becomes
if x.is_none():
    x = y
```

**Type Rules:**
- `a ?? b` where `a: Option[T]`, `b: T` → result is `T` (unwrapped)
- `a ?? b` where both `a: T`, `b: T` → treat as `a != nil ? a : b`

**Recommendation:** 🎯 **HIGH PRIORITY ADD**

**MUST** pair with optional chaining (#12) for maximum value.

**Combined Example:**
```simple
# Chaining + coalescing
let display_name = user?.profile?.display_name
                   ?? user?.username
                   ?? "Guest"

# Replaces 20+ lines of match/if statements
```

**Priority:** **HIGH** - Implements optional handling ergonomics

---

## Category E: Error Propagation

### 14. Propagate Operator ❌ **MISSING**

**Status:** Not implemented

**Current Verbose Approach:**
```simple
# Current: explicit error handling
fn read_config(path: String) -> Result[Config, Error]:
    let contents = match read_file(path):
        case Ok(c): c
        case Err(e): return Err(e)

    let parsed = match parse_json(contents):
        case Ok(p): p
        case Err(e): return Err(e)

    let validated = match validate(parsed):
        case Ok(v): v
        case Err(e): return Err(e)

    return Ok(transform(validated))
```

**Proposed Syntax (Rust-style):**
```simple
fn read_config(path: String) -> Result[Config, Error]:
    let contents = read_file(path)?      # Returns Err early if error
    let parsed = parse_json(contents)?   # Returns Err early if error
    let validated = validate(parsed)?     # Returns Err early if error
    return Ok(transform(validated))
```

**Operator:** `?` postfix
- Unwraps `Ok` value
- Propagates `Err` by early return
- Only works in functions returning `Result`

**Semantics:**
```simple
# Desugaring
let x = operation()?

# Becomes
let x = match operation():
    case Ok(value): value
    case Err(e): return Err(e)
```

**Type Rules:**
- `expr?` where `expr: Result[T, E]` and function returns `Result[U, E]`
  - Result: unwrapped value of type `T`
  - Side effect: may return `Err(e)` from function
- Error type `E` must be compatible with function's error type

**Also Works for Option:**
```simple
fn find_nested(id: i64) -> Option[Value]:
    let user = find_user(id)?       # Returns None if not found
    let profile = user.profile?     # Returns None if None
    let value = profile.data?       # Returns None if None
    return Some(value.get_key("x"))
```

**Recommendation:** 🎯 **HIGHEST PRIORITY**

This is **the single highest LOC-reduction feature** for error handling.

**Impact Example:**
```simple
# Before (30+ lines)
fn process_pipeline(input: Input) -> Result[Output, Error]:
    let step1 = match parse(input):
        case Ok(v): v
        case Err(e): return Err(e)

    let step2 = match validate(step1):
        case Ok(v): v
        case Err(e): return Err(e)

    let step3 = match transform(step2):
        case Ok(v): v
        case Err(e): return Err(e)

    let step4 = match save(step3):
        case Ok(v): v
        case Err(e): return Err(e)

    return Ok(finalize(step4))

# After (7 lines)
fn process_pipeline(input: Input) -> Result[Output, Error]:
    let step1 = parse(input)?
    let step2 = validate(step1)?
    let step3 = transform(step2)?
    let step4 = save(step3)?
    return Ok(finalize(step4))
```

**Implementation Notes:**
- Must verify function return type is `Result[_, E]` or `Option[_]`
- Error in non-Result function → compile error
- Can chain: `file.read()?.parse()?.validate()?`

---

## Category F: Function/Lambda Brevity

### 15. Arrow Lambdas ✅ **DONE**

**Status:** Already implemented (backslash syntax)

**Simple Syntax:**
```simple
# Single parameter
xs.map(\x: x * 2)

# Multiple parameters
pairs.map(\a, b: a + b)

# With type annotations
xs.filter(\x: i64: x > 0)

# Trailing block syntax
xs.each \x:
    print(x)
    process(x)
```

**Recommendation:** ✓ Keep as-is. Concise and works well.

**Note:** Backslash `\` is distinctive (borrowed from Haskell/ML family).

---

### 16. Expression-Bodied Functions ❌ **MISSING**

**Status:** Not implemented (all functions require block)

**Current:**
```simple
fn add(a: i64, b: i64) -> i64:
    return a + b

fn square(x: i64) -> i64:
    return x * x
```

**Proposed (C#-style `=>`):**
```simple
fn add(a: i64, b: i64) -> i64 => a + b

fn square(x: i64) -> i64 => x * x

# Also for methods
class Calculator:
    fn add(a: i64, b: i64) -> i64 => a + b
    fn multiply(a: i64, b: i64) -> i64 => a * b
```

**Benefits:**
- **Reduces ceremony** for simple functions
- **Single expression** body (no need for `return`)
- **Common pattern** (C#, Kotlin, Scala)

**Grammar:**
```
function_def: 'fn' identifier params ['->' type] ('=>' expression | ':' block)
```

**Constraints:**
- Must have return type annotation (needed for type inference)
- Body must be single expression
- No statements allowed in `=>` form

**Recommendation:** 🔧 **MEDIUM PRIORITY ADD**

Nice ergonomic improvement, especially for:
- One-liner functions
- Functional programming patterns
- Method definitions in classes/traits

**Implementation:** Straightforward desugaring to block with return.

---

## Category G: String & Literal Ergonomics

### 17. String Interpolation ✅ **DONE**

**Status:** Already implemented (default for `"..."`)

**Simple Syntax:**
```simple
let name = "World"
let count = 42
let msg = "Hello, {name}! Count is {count + 1}"
# Result: "Hello, World! Count is 43"

# Escape braces
let template = "Use {{ and }} for literal braces"
```

**Recommendation:** ✓ Keep as-is. Excellent design choice.

---

### 18. Raw/Multiline Strings ✅ **DONE**

**Status:** Already implemented

**Simple Syntax:**
```simple
# Raw strings (single quotes) - no interpolation/escaping
let regex = '[a-z]+\d{2,3}'
let path = 'C:\Users\name'

# Multiline strings (triple quotes)
let doc = """
This is a multi-line
documentation string.
No interpolation here.
"""
```

**Recommendation:** ✓ Keep as-is. Well-designed.

---

## Recommended Adoption Priority

### Tier 1: Essential High-Leverage Features (Implement First)

| Priority | Feature | LOC Impact | Complexity | Syntax |
|----------|---------|------------|------------|--------|
| 🥇 **1** | Error propagation `?` | ⭐⭐⭐⭐⭐ | Medium | `operation()?` |
| 🥈 **2** | Optional chaining `?.` | ⭐⭐⭐⭐⭐ | Medium | `user?.profile?.name` |
| 🥉 **3** | Nullish coalescing `??` | ⭐⭐⭐⭐ | Low | `value ?? default` |
| 4 | Pipeline operator `\|>` | ⭐⭐⭐⭐ | Medium | `x \|> f \|> g` |
| 5 | Placeholder `_` | ⭐⭐⭐⭐ | Medium | `xs.map(_ * 2)` |

**Rationale:**
- **Error propagation**: Eliminates massive boilerplate in error-heavy code
- **Optional chaining**: Essential for Option ergonomics
- **Nullish coalescing**: Pairs with optional chaining
- **Pipeline + placeholder**: Transform nested calls into linear flow

**Combined Impact Example:**
```simple
# All 5 features together
let result = fetch_config()?
    |> parse(_)?
    |> validate(_)?
    |> user?.apply_overrides(_) ?? _
    |> save(_)?
```

### Tier 2: Nice-to-Have Improvements

| Priority | Feature | LOC Impact | Complexity | Syntax |
|----------|---------|------------|------------|--------|
| 6 | Expression-bodied fn | ⭐⭐⭐ | Low | `fn f(x) => x * 2` |
| 7 | Range expressions | ⭐⭐⭐ | Low | `for i in 0..10` |
| 8 | Slicing syntax | ⭐⭐⭐ | Medium | `xs[1:5:2]` |
| 9 | Assignment expr `:=` | ⭐⭐ | Low | `if (m := re.match(...))` |

**Rationale:**
- **Expression-bodied functions**: Clean syntax for common pattern
- **Ranges/slicing**: Common in data processing
- **Assignment expr**: Useful but easy to abuse

### Tier 3: Defer to Stdlib

| Feature | Implementation | Notes |
|---------|----------------|-------|
| Fused filter+map | Add `filter_map()` method | Stdlib, not syntax |
| Method chains | Already works | No changes needed |

---

## Implementation Roadmap

### Phase 1: Core Error/Optional Handling (Sprint 1-2)

**Goal:** Eliminate 80% of error handling boilerplate

**Tasks:**
1. ✅ Implement `?` postfix operator for Result/Option
   - Parser: Add postfix `?` to expression grammar
   - Type checker: Verify function return type compatibility
   - Codegen: Desugar to match + early return
   - Tests: Error propagation chains, type errors

2. ✅ Implement `?.` optional chaining
   - Parser: Add `?.` operator (precedence with `.`)
   - Type checker: Propagate Option through chain
   - Codegen: Desugar to nested matches
   - Tests: Deep chains, method calls, edge cases

3. ✅ Implement `??` and `??=` nullish coalescing
   - Parser: Add `??` binary operator (low precedence)
   - Parser: Add `??=` assignment operator
   - Type checker: Verify types (Option[T] ?? T → T)
   - Codegen: Desugar to match for `??`, conditional assign for `??=`
   - Tests: Chaining with `?.`, nested usage

**Deliverables:**
- Grammar updates
- Type system updates
- Codegen for all three operators
- Comprehensive test suite (50+ tests)
- Documentation updates

**Success Criteria:**
```simple
# Can write concise error handling
fn process(path: String) -> Result[Data, Error]:
    let config = read_config(path)?
    let user = find_user(config.user_id)?
    let profile = user?.profile?.data ?? default_profile()
    return Ok(process_profile(profile)?)
```

### Phase 2: Dataflow Improvements (Sprint 3-4)

**Goal:** Linear transformation pipelines

**Tasks:**
1. ✅ Implement `|>` pipeline operator
   - Parser: Add `|>` binary operator (low precedence)
   - Type checker: Thread types through pipeline
   - Codegen: Desugar to nested function calls
   - Tests: Chains, precedence, type errors

2. ✅ Implement `_` placeholder syntax
   - Parser: Add `_` as special identifier in arg position
   - Type checker: Detect placeholder, create implicit lambda
   - Codegen: Desugar to lambda with generated parameter
   - Tests: Single arg, multiple uses, error cases

**Deliverables:**
- Pipeline + placeholder working together
- Integration tests with collections
- Documentation with examples

**Success Criteria:**
```simple
# Can write point-free transformations
let result = data
    |> parse()
    |> filter(_ > 0)
    |> map(_ * 2)
    |> take(10)
    |> sum()
```

### Phase 3: Quality of Life (Sprint 5)

**Goal:** Additional ergonomic improvements

**Tasks:**
1. ✅ Expression-bodied functions
   - Parser: Add `=> expr` alternative to `: block`
   - Desugar to block with return
   - Tests: Type inference, edge cases

2. ✅ Range expressions
   - Runtime: Implement Range type
   - Type checker: Support `..` and `..<` operators
   - Codegen: Create Range objects
   - Tests: Iteration, edge cases

3. ⚠️ Slicing syntax (evaluate)
   - Parser: Add slice notation `[start:end:step]`
   - Runtime: Implement slicing methods
   - Tests: Various slice patterns

4. ⚠️ Assignment expressions (evaluate carefully)
   - Parser: Add `:=` operator
   - Scoping rules: Variable scope in conditional block
   - Lint rules: Warn on misuse
   - Tests: If/while usage, scoping

**Deliverables:**
- Expression-bodied functions
- Range expressions
- Decision on slicing/assignment expressions
- Updated documentation

---

## Grammar Updates Summary

### New Operators (by precedence, lowest to highest)

| Operator | Associativity | Precedence | Description |
|----------|---------------|------------|-------------|
| `\|>` | Left | 1 (lowest) | Pipeline |
| `??` | Left | 2 | Nullish coalescing |
| `??=` | Right | 2 | Nullish coalescing assignment |
| `:=` | Right | 2 | Assignment expression (optional) |
| `..`, `..<` | Left | 10 | Range operators |
| `?.` | Left | 18 | Optional chaining |
| `?` | Postfix | 19 | Error/option propagation |

### New Expression Forms

```javascript
// Pipeline
pipeline_expr: expression ('|>' expression)+

// Optional chaining
optional_chain: expression ('?.' identifier)+

// Nullish coalescing
nullish_coalesce: expression '??' expression

// Error propagation
try_propagate: expression '?'

// Placeholder lambda (implicit)
placeholder: '_'

// Expression-bodied function
function_def: 'fn' identifier params ['->' type] ('=>' expression | ':' block)

// Range expression
range_expr: expression ('..' | '..<') expression

// Slice (optional)
slice_expr: expression '[' [expression] ':' [expression] [':' [expression]] ']'

// Assignment expression (optional)
assign_expr: '(' identifier ':=' expression ')'
```

---

## LL(1) Compatibility Notes

All proposed features maintain LL(1) parsing with single-token lookahead:

| Feature | LL(1) Strategy |
|---------|----------------|
| Pipeline `\|>` | Prefix operator, no ambiguity |
| Optional chain `?.` | Prefix operator after `.` |
| Nullish `??` | Prefix operator, distinct from `?` |
| Propagate `?` | Postfix operator, follows expression |
| Placeholder `_` | Detected in arg position by context |
| Expression fn `=>` | After params, alternates with `:` |
| Range `..` | Binary operator, no conflicts |
| Slice `[:]` | Subscript context, `:` is trigger |

**No lookahead conflicts** with existing grammar.

---

## References

### Language Features

- **Rust** `?` operator: [Error Propagation](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html#propagating-errors-with-the--operator)
- **JavaScript** `?.` and `??`: [Optional Chaining](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Optional_chaining), [Nullish Coalescing](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Nullish_coalescing)
- **Elixir** `|>`: [Pipeline Operator](https://elixir-lang.org/getting-started/enumerables-and-streams.html#the-pipe-operator)
- **Kotlin** `_` placeholder: [Lambda Syntax](https://kotlinlang.org/docs/lambdas.html#it-implicit-name-of-a-single-parameter)
- **C#** expression-bodied members: [Expression Bodies](https://learn.microsoft.com/en-us/dotnet/csharp/programming-guide/statements-expressions-operators/expression-bodied-members)
- **Python** `:=` walrus: [Assignment Expressions](https://peps.python.org/pep-0572/)

### Related Simple Documentation

- [Syntax Specification](../spec/syntax.md)
- [Types Specification](../spec/types.md)
- [Grammar Definition](../spec/parser/lexer_parser_grammar_expressions.md)
- [Statement Container Grammars](statement_container_grammars.md)

---

## Conclusion

Simple already has strong foundations:
- ✅ Comprehensions
- ✅ Spread syntax
- ✅ Destructuring
- ✅ Pattern matching
- ✅ String interpolation
- ✅ Arrow lambdas

**Recommended additions** for maximum impact:

**Tier 1 (Essential):**
1. Error propagation `?` - Eliminates error handling boilerplate
2. Optional chaining `?.` - Ergonomic Option handling
3. Nullish coalescing `??` - Clean defaults
4. Pipeline `|>` - Linear dataflow
5. Placeholder `_` - Concise lambdas

**Tier 2 (Nice-to-have):**
6. Expression-bodied functions `=>`
7. Range expressions `0..n`
8. Slicing `xs[1:5]`
9. Assignment expressions `:=` (use carefully)

These additions would put Simple's ergonomics on par with Rust (error handling) + Kotlin (null safety) + Elixir (pipelines), while maintaining its Python-like readability.

**Estimated LOC reduction:** 30-50% in typical codebases with heavy error/optional handling and data transformations.

---

## Unified Design: Last Value Rule & Expression-Oriented Syntax

**Status:** Design Proposal
**Updated:** 2026-01-06

This section presents a **unified, minimal design** that achieves maximum concision with a single core principle: **Last Value Rule**. This design is inspired by Ruby's implicit returns, Kotlin's lambda expressions, and Scala's for-comprehensions.

### Core Principle: Last Value Rule

**Any block introduced by `=>:` is a value block:**
- The **last expression statement** in the block is the block's value (implicit return/yield)
- No `return` or `yield` keyword needed in the common case
- Aligned with Ruby's "method returns last evaluated expression" and Kotlin's "last expression in lambda"

---

### 1. Universal Lambda Syntax: `\params: body`

**Single form for all lambdas** - no special syntax variations

**Syntax:**
```simple
# Single parameter
inc = \x: x + 1

# Multiple parameters
add = \a, b: a + b

# Zero parameters (thunk)
thunk = \: expensive()

# Multi-line (last line is the value)
square_norm = \x:
    let y = normalize(x)
    y * y                    # Implicit return
```

**Eliminates:**
- No `||:` syntax needed
- No explicit `return` in common case
- Consistent with "last value rule"

**Grammar:**
```
lambda_expr: '\' [param_list] ':' (expression | block)
block: INDENT statements DEDENT
```

**Compatibility:** ✅ Already matches Simple's `\x: expr` syntax

---

### 2. For/While: Statement vs Yieldable Forms

**Two forms distinguished by separator:**

#### A) Statement Loops (Side Effects): `:`

Traditional loops for side effects, no value returned:

```simple
# For loop - side effects
for x in xs:
    log(x)

# While loop - side effects
while cond:
    step()
```

**Returns:** `nil` (or `()` unit type)

#### B) Yieldable Loops (Expression Form): `=>`/`=>:`

**Key innovation:** Loop returns `Yieldable[T]`, last expression is yielded element

**Single-expression body:**
```simple
# Map-style
ys = for x in xs => f(x)

# Filter + map
zs = for x in xs if p(x) => f(x)

# While yielding
nums = while i < n => (i, i += 1).0
```

**Block body (last expression is yielded):**
```simple
# Multi-line transformation
ys = for x in xs if p(x) =>:
    let y = normalize(x)
    y * y                     # Implicit yield

# Yieldable while with block
nums = while i < n =>:
    let v = i
    i += 1
    v                         # Implicit yield
```

**Why `=>` separator:**
- **Prevents accidental yielding** when you intended side-effect loop
- **Extremely compact** for common case
- **Clear intent** - `=>` signals "produces values"

**Desugaring:**
```simple
# This
ys = for x in xs if p(x) => f(x)

# Becomes
ys = xs.withFilter(\x: p(x)).map(\x: f(x))
```

**Grammar:**
```
# Statement form
for_stmt: 'for' pattern 'in' expression ':' block

# Yieldable form (expression)
for_expr: 'for' pattern 'in' expression [guard] '=>' expression
for_expr: 'for' pattern 'in' expression [guard] '=>:' block

# Same for while
while_stmt: 'while' expression ':' block
while_expr: 'while' expression '=>' expression
while_expr: 'while' expression '=>:' block
```

**Compatibility:** ⚠️ **NEW** - Simple currently has comprehensions `[for x in xs: f(x)]`, need to add expression form

---

### 3. Switch as Expression with Last-Value Arms

**Switch returns a value** - each arm's last expression is the arm value

**Syntax:**

**Expression arms (`=>`)**:
```simple
label = switch code:
    case 200 => "OK"
    case 404 => "Not Found"
    case _   => "Other"
```

**Block arms (`=>:`)**:
```simple
label = switch code:
    case 200 => "OK"
    case _ =>:
        let msg = "Other(" + code.str() + ")"
        msg                   # Implicit arm value
```

**Mixed arms:**
```simple
result = switch value:
    case 0 => "zero"
    case n if n > 0 => "positive"
    case n =>:
        let abs_n = -n
        "negative: {abs_n}"
```

**Grammar:**
```
switch_expr: 'switch' expression ':' INDENT case_arm+ DEDENT
case_arm: 'case' pattern [guard] '=>' expression
case_arm: 'case' pattern [guard] '=>:' block
```

**Compatibility:** ⚠️ **EXTENDS** - Simple has `match` statement, need to add expression form with `=>`

---

### 4. Expression-Bodied Functions

**Consistent with lambda and switch arm syntax:**

```simple
# Single expression (with =>)
fn add(a: i64, b: i64) -> i64 => a + b

fn square(x: i64) -> i64 => x * x

# Block form (with =>:, implicit return)
fn complex(x: i64) -> i64 =>:
    let y = normalize(x)
    y * y                     # Implicit return

# Traditional block (with :, explicit return)
fn traditional(x: i64) -> i64:
    let y = normalize(x)
    return y * y              # Explicit return
```

**Rule:**
- `fn ... =>` - single expression, implicit return
- `fn ... =>:` - block, last value is return
- `fn ... :` - traditional block, explicit `return` required

**Grammar:**
```
function_def: 'fn' identifier params ['->' type] function_body
function_body: '=>' expression              # Expression form
function_body: '=>:' block                  # Value block form
function_body: ':' block                    # Statement block form
```

**Compatibility:** ⚠️ **NEW** - Extends current `: block` with `=> expr` and `=>: block`

---

### 5. First-Class Map/Filter/Reduce via Desugaring

**Make `for` syntax sugar over higher-order operations** (Scala-style):

```simple
# Surface syntax
ys = for x in xs if p(x) => f(x)

# Desugars to
ys = xs.withFilter(\x: p(x)).map(\x: f(x))

# Nested loops
result = for x in xs =>:
    for y in ys => (x, y)

# Desugars to
result = xs.flatMap(\x: ys.map(\y: (x, y)))
```

**Requirements:**
- Collections implement `map`, `flatMap`, `withFilter`
- `Yieldable[T]` protocol with iterator support
- Lazy evaluation by default (like Scala's `view`)

**Benefits:**
- **Short comprehension-like syntax**
- **Fully first-class operations** underneath
- **Composable** with existing collection methods
- **Optimizable** by compiler

---

### 6. Optional Advanced Mode: Multi-Yield Generators

**For true generator semantics** with multiple yields per iteration:

```simple
# Multi-yield generator (with =>*)
ys = for x in xs =>*:
    if a(x): yield f(x)
    if b(x): yield g(x)
    # Can yield 0, 1, or 2 values per iteration
```

**Comparison:**
- `=>:` - **One element per iteration** (map-style, default, shortest)
- `=>*:` - **Multiple yields** (generator-style, explicit marker)

**Recommendation:** Keep `=>:` as default for 80% case (map/filter), use `=>*:` only when needed

**Grammar:**
```
for_generator: 'for' pattern 'in' expression '=>*:' block
# Block contains explicit 'yield' statements
```

**Compatibility:** ⚠️ **NEW** - Explicit generator support

---

### Summary: Unified Design Advantages

| Feature | Old Syntax | New Syntax | Benefit |
|---------|-----------|------------|---------|
| Lambda | `\x: x + 1` | `\x: x + 1` | ✅ No change |
| Multi-line lambda | `\x: return x * x` | `\x: x * x` | Implicit return |
| Map operation | `xs.map(\x: f(x))` | `for x in xs => f(x)` | Comprehension-style |
| Filter + map | `xs.filter(p).map(f)` | `for x in xs if p(x) => f(x)` | One expression |
| Function | `fn f(x): return x` | `fn f(x) => x` | Remove ceremony |
| Switch expr | `match x: case 1: ...` | `switch x: case 1 => ...` | Expression form |

**Core Rules (Minimal):**
1. ✅ Last value rule: Last expression in `=>:` block is the value
2. ✅ Statement vs expression: `:` for statements, `=>` for expressions
3. ✅ Consistent operators: `=>` (single expr), `=>:` (value block)
4. ✅ No special cases: Works for lambdas, functions, loops, switch

**LOC Reduction Examples:**

Before:
```simple
# Traditional (15 lines)
let results = []
for x in xs:
    if pred(x):
        let y = transform(x)
        results.push(y)
```

After:
```simple
# Unified design (1 line)
let results = for x in xs if pred(x) =>: transform(x)
```

**Compatibility Impact:**

| Feature | Simple Current | Change Required | Breaking? |
|---------|---------------|-----------------|-----------|
| Lambda `\x: expr` | ✅ Exists | Extend last-value rule | No |
| Comprehension `[for ...]` | ✅ Exists | Keep as-is | No |
| Expression `for` | ❌ Missing | Add `for ... =>` form | No |
| Switch expression | ⚠️ Partial | Add `case ... =>` arms | No |
| Expr-bodied fn | ❌ Missing | Add `fn ... =>` form | No |
| Generator `yield` | ⚠️ Partial | Add `=>*:` form | No |

**Implementation Priority:**

1. **Phase 1:** Last value rule for `=>:` blocks
2. **Phase 2:** Expression-bodied functions `fn ... =>`
3. **Phase 3:** Yieldable loops `for ... =>`
4. **Phase 4:** Switch expressions `case ... =>`
5. **Phase 5:** Multi-yield generators `=>*:` (optional)

---

### Grammar Summary: New Productions

```javascript
// Value separator (expression from block)
'=>'   // Single expression follows
'=>:'  // Value block follows (last expr is value)
'=>*:' // Generator block follows (explicit yields)

// Lambda (unchanged, but last-value rule applies to blocks)
lambda_expr: '\' [param_list] ':' (expression | value_block)

// For expression (new)
for_expr: 'for' pattern 'in' expression [guard] '=>' expression
for_expr: 'for' pattern 'in' expression [guard] '=>:' value_block
for_generator: 'for' pattern 'in' expression '=>*:' generator_block

// While expression (new)
while_expr: 'while' expression '=>' expression
while_expr: 'while' expression '=>:' value_block

// Switch expression (extends match)
switch_expr: 'switch' expression ':' INDENT case_arm+ DEDENT
case_arm: 'case' pattern [guard] '=>' expression
case_arm: 'case' pattern [guard] '=>:' value_block

// Function (extends current)
function_def: 'fn' identifier params ['->' type] function_body
function_body: '=>' expression              // New: expression form
function_body: '=>:' value_block            // New: value block
function_body: ':' statement_block          // Current: statement form

// Value block (last expression is the value)
value_block: INDENT statements expression DEDENT
```

### References for Unified Design

- **Ruby** implicit returns: [Ruby Methods](https://ruby-doc.org/core-3.1.0/doc/syntax/methods_rdoc.html)
- **Kotlin** last expression in lambda: [Lambda Expressions](https://kotlinlang.org/docs/lambdas.html#lambda-expression-syntax)
- **Scala** for-comprehensions: [For Expressions](https://docs.scala-lang.org/tour/for-comprehensions.html)
- **C#** switch expressions: [Switch Expressions](https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/operators/switch-expression)
- **Rust** implicit returns: [Functions](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html#functions-with-return-values)
