# Python Feature Migration

Analysis of Python syntax features for Simple language adoption.

## Guiding Principles

1. **LL(1) Grammar** - Must be parseable with single-token lookahead
2. **Formal Verification** - Semantics must be precisely definable in Lean 4
3. **Existing Syntax** - Prefer Simple's current syntax when better than Python

---

## Already Implemented (Better Than Python)

### Conditional Expression

**Python:**
```python
result = value if condition else default  # Condition in middle
```

**Simple (Current - Better):**
```simple
let result = if condition: value else: default  # Condition first
```

**Why Simple is Better:**
- Reads left-to-right logically
- Condition comes first (like statement if)
- Starts with keyword `if` → LL(1) unambiguous
- Easier formal verification (standard conditional semantics)

**Grammar:**
```
if_expr := 'if' expr ':' expr 'else' ':' expr
```

### String Interpolation

**Python:**
```python
f"Hello {name}, you have {count} items"
```

**Simple (Current):**
```simple
"Hello {name}, you have {count} items"  # Default interpolation
'raw string {not interpolated}'          # Raw strings
```

**Status:** ✅ Already better - interpolation is default

### Pattern Matching

**Python 3.10+:**
```python
match command:
    case "quit":
        exit()
    case ["move", x, y]:
        move(x, y)
```

**Simple (Current):**
```simple
match command:
    "quit":
        exit()
    ["move", x, y]:
        move(x, y)
```

**Status:** ✅ Already implemented

### Lambda Expressions

**Python:**
```python
double = lambda x: x * 2
```

**Simple (Current - Better):**
```simple
let double = \x: x * 2
```

**Why Simple is Better:**
- `\` is unambiguous (no confusion with `:` in dicts)
- LL(1) parseable
- ML-family inspiration (well-studied)

### In Operator

**Python:**
```python
if x in items:
if key in dict:
```

**Simple (Current):**
```simple
if x in items:
if key in dict:
```

**Status:** ✅ Already implemented

---

## Recommended Additions

### 1. List Comprehension

**Python:**
```python
squares = [x**2 for x in range(10)]
evens = [x for x in nums if x % 2 == 0]
```

**Proposed Simple Syntax:**
```simple
let squares = [x**2 for x in 0..10]
let evens = [x for x in nums if x % 2 == 0]
```

**Grammar (LL(1)):**
```
comprehension := '[' expr 'for' pattern 'in' expr ('if' expr)? ']'
```

**Analysis:**
- ✅ LL(1): `[` followed by expr, then `for` keyword distinguishes from array literal
- ✅ Formal: Desugars to `map` + `filter` (well-defined semantics)
- ⚠️ Ambiguity: `[x for ...]` vs `[x, y, z]` - resolved by lookahead to `for`

**Verification:**
```lean
-- Desugar: [f(x) for x in xs if p(x)] ≡ xs.filter(p).map(f)
theorem comprehension_equiv (xs : List α) (p : α → Bool) (f : α → β) :
  [f(x) for x in xs if p(x)] = (xs.filter p).map f
```

**Priority:** High

---

### 2. Dict Comprehension

**Python:**
```python
word_len = {w: len(w) for w in words}
```

**Proposed Simple Syntax:**
```simple
let word_len = {w: len(w) for w in words}
```

**Grammar (LL(1)):**
```
dict_comprehension := '{' expr ':' expr 'for' pattern 'in' expr ('if' expr)? '}'
```

**Analysis:**
- ✅ LL(1): `{` + expr + `:` + expr + `for` distinguishes from dict literal
- ✅ Formal: Desugars to fold/reduce

**Priority:** High

---

### 3. Unpacking Assignment

**Python:**
```python
a, b = b, a           # Swap
first, *rest = items  # Head/tail
x, y, z = point       # Destructure
```

**Proposed Simple Syntax:**
```simple
a, b = b, a           # Swap
let first, *rest = items  # Head/tail
let x, y, z = point       # Destructure
let _, y, _ = triple      # Ignore with _
```

**Grammar (LL(1)):**
```
unpack_target := pattern (',' pattern)* (',' '*' IDENT)?
assignment := unpack_target '=' expr
```

**Analysis:**
- ✅ LL(1): Tuple pattern on left side of `=`
- ✅ Formal: Pattern matching semantics (already defined)
- ⚠️ `*rest` splat needs special handling

**Verification:**
```lean
-- Swap equivalence
theorem swap_correct (a b : α) :
  let (a', b') := (b, a) in a' = b ∧ b' = a
```

**Priority:** High

---

### 4. Chained Comparisons

**Python:**
```python
0 < x < 10
a <= b <= c
```

**Proposed Simple Syntax:**
```simple
0 < x < 10      # Same as Python
a <= b <= c
```

**Grammar (LL(1)):**
```
comparison := expr (comp_op expr)+
comp_op := '<' | '>' | '<=' | '>=' | '==' | '!='
```

**Desugaring:**
```simple
# 0 < x < 10 becomes:
0 < x and x < 10

# But x is only evaluated once:
let _t = x in 0 < _t and _t < 10
```

**Analysis:**
- ✅ LL(1): Chain of comparison operators
- ✅ Formal: Desugars to conjunction with single evaluation
- ⚠️ Must ensure middle expression evaluated only once

**Verification:**
```lean
theorem chain_compare (a b c : Int) :
  (a < b < c) ↔ (a < b ∧ b < c)
```

**Priority:** Medium

---

### 5. Slicing

**Python:**
```python
items[1:3]    # Elements 1, 2
items[:3]     # First 3
items[3:]     # From 3 to end
items[::2]    # Every 2nd
items[::-1]   # Reversed
```

**Proposed Simple Syntax:**
```simple
items[1:3]    # Elements 1, 2
items[:3]     # First 3
items[3:]     # From 3 to end
items[::2]    # Every 2nd (step)
items[::-1]   # Reversed
```

**Grammar (LL(1)):**
```
index_expr := expr '[' slice ']'
slice := expr? ':' expr? (':' expr?)?   # start:end:step
       | expr                            # single index
```

**Analysis:**
- ✅ LL(1): `:` distinguishes slice from index
- ✅ Formal: Well-defined list operations
- ⚠️ Need to handle negative indices

**Priority:** High

---

### 6. Negative Indexing

**Python:**
```python
items[-1]     # Last element
items[-2]     # Second to last
```

**Proposed Simple Syntax:**
```simple
items[-1]     # Last element
items[-2]     # Second to last
```

**Analysis:**
- ✅ LL(1): Unary minus in index position
- ✅ Formal: `items[-n] ≡ items[len(items) - n]`
- ⚠️ Runtime bounds check needed

**Verification:**
```lean
theorem neg_index (xs : List α) (n : Nat) (h : n ≤ xs.length) :
  xs[-n] = xs[xs.length - n]
```

**Priority:** High

---

### 7. Truthiness (Implicit Bool Conversion)

**Python:**
```python
if items:        # True if non-empty
if name:         # True if non-empty string
if count:        # True if non-zero
```

**Proposed Simple Syntax - REJECTED:**
```simple
# NOT recommended - explicit is better
if items:        # Ambiguous: is this checking existence or non-empty?
```

**Simple Alternative (Current - Better):**
```simple
if items.len() > 0:    # Explicit
if not items.is_empty():
if name != "":
if count != 0:
```

**Analysis:**
- ❌ Truthiness is implicit and error-prone
- ❌ Hard to verify: what is "truthy" for custom types?
- ✅ Simple's explicit checks are clearer and verifiable

**Formal Verification Issue:**
```lean
-- Truthiness requires defining bool conversion for all types
-- This is ad-hoc and hard to reason about
class Truthy (α : Type) where
  toBool : α → Bool

-- Custom types: what's truthy?
instance : Truthy MyType where
  toBool := ???  -- Undefined behavior
```

**Priority:** Not Recommended

---

### 8. Walrus Operator (Assignment Expression)

**Python:**
```python
if (n := len(items)) > 10:
    print(f"Too many: {n}")
```

**Proposed Simple Syntax:**
```simple
if (let n = len(items)) > 10:
    print "Too many: {n}"
```

**Alternative (Current - Clearer):**
```simple
let n = len(items)
if n > 10:
    print "Too many: {n}"
```

**Analysis:**
- ⚠️ LL(1) possible but complex: `(let` starts assignment expression
- ⚠️ Formal: Side effects in expressions complicate verification
- ✅ Current two-line version is clearer

**Priority:** Low (Nice to have, not essential)

---

### 9. Spread/Rest Operators

**Python:**
```python
combined = [*list1, *list2]
merged = {**dict1, **dict2}
def func(*args, **kwargs):
```

**Proposed Simple Syntax:**
```simple
let combined = [*list1, *list2]
let merged = {**dict1, **dict2}
fn func(*args, **kwargs):
```

**Grammar (LL(1)):**
```
spread_elem := '*' expr           # In arrays
spread_kv := '**' expr            # In dicts
rest_param := '*' IDENT           # In function params
kwargs_param := '**' IDENT
```

**Analysis:**
- ✅ LL(1): `*` and `**` are unambiguous prefixes
- ✅ Formal: Well-defined concatenation/merge semantics

**Priority:** Medium

---

### 10. Context Managers

**Python:**
```python
with open("file.txt") as f:
    data = f.read()
```

**Proposed Simple Syntax:**
```simple
with open("file.txt") as f:
    let data = f.read()
```

**Grammar (LL(1)):**
```
with_stmt := 'with' expr 'as' IDENT ':' block
```

**Desugaring:**
```simple
# with resource as r: body
# becomes:
let r = resource
try:
    body
finally:
    r.close()
```

**Analysis:**
- ✅ LL(1): `with` keyword starts statement
- ✅ Formal: Resource acquisition/release pattern
- ✅ Verifiable: Can prove resource is always released

**Verification:**
```lean
theorem with_releases (r : Resource) (body : Resource → IO α) :
  with r as x: body(x)
  → r.is_released
```

**Priority:** High (Resource safety)

---

### 11. Decorators vs Attributes

Simple supports **both** decorators and attributes with different purposes:

| Aspect | Decorator `@name` | Attribute `#[name]` |
|--------|-------------------|---------------------|
| Behavior | **Active** - transforms code | **Passive** - metadata only |
| Execution | Runs at definition time | Read by compiler |
| Use case | Wrapping, caching, logging | Hints, warnings, derive |

#### Decorators (Active Transformation)

**Python:**
```python
@log_calls
@cached
def process(data):
    ...
```

**Proposed Simple Syntax:**
```simple
@log_calls
@cached
fn process(data):
    ...
```

**Grammar (LL(1)):**
```
decorator := '@' expr NEWLINE
decorated := decorator+ (fn_def | class_def)
```

**Desugaring:**
```simple
# @decorator fn foo(): body
# becomes:
fn foo(): body
foo = decorator(foo)
```

**Analysis:**
- ✅ LL(1): `@` is unambiguous prefix
- ⚠️ Formal: Higher-order function transformation
- ⚠️ Type inference may be complex

**Priority:** Medium

#### Attributes (Passive Metadata)

**Rust-style:**
```rust
#[inline]
#[deprecated(since = "1.0", note = "use new_func instead")]
fn old_func() { }
```

**Proposed Simple Syntax:**
```simple
#[inline]
#[deprecated(since: "1.0", note: "use new_func instead")]
fn old_func():
    ...

#[derive(Debug, Clone)]
struct Point:
    x: f64
    y: f64
```

**Grammar (LL(1)):**
```
attribute := '#[' IDENT ('(' attr_args ')')? ']' NEWLINE
attr_args := attr_arg (',' attr_arg)*
attr_arg := IDENT ':' expr | expr
```

**Common Attributes:**
| Attribute | Purpose |
|-----------|---------|
| `#[inline]` | Hint to inline function |
| `#[cold]` | Unlikely to be called (branch prediction) |
| `#[deprecated]` | Warn on use |
| `#[must_use]` | Warn if return value ignored |
| `#[derive(...)]` | Auto-implement traits |
| `#[test]` | Mark as test function |
| `#[cfg(...)]` | Conditional compilation |

**Analysis:**
- ✅ LL(1): `#[` is unambiguous start
- ✅ Formal: Pure metadata, no runtime behavior
- ✅ Easy to verify: attributes don't change semantics

**Combined Example:**
```simple
#[inline]                    # Attribute: compiler hint
#[deprecated(note: "use v2")] # Attribute: warning
@log_calls                   # Decorator: wraps function
@cached(ttl: 60)             # Decorator: adds caching
fn expensive_calc(x: i64) -> i64:
    ...
```

**Priority:** Medium (Decorators), Medium (Attributes)

---

### 12. For-Else

**Python:**
```python
for item in items:
    if item.matches():
        break
else:
    print("No match found")
```

**Proposed Simple Syntax:**
```simple
for item in items:
    if item.matches():
        break
else:
    print "No match found"
```

**Analysis:**
- ✅ LL(1): `else` after `for` block
- ✅ Formal: "else runs if no break" is clear semantics
- ⚠️ Rarely used, confusing to some developers

**Priority:** Low

---

## Summary Table

| Feature | Python Syntax | Simple Syntax | LL(1) | Verifiable | Priority |
|---------|--------------|---------------|-------|------------|----------|
| Conditional | `x if c else y` | `if c: x else: y` ✓ | ✅ | ✅ | Done |
| F-strings | `f"..."` | `"..."` ✓ | ✅ | ✅ | Done |
| Pattern match | `match/case` | `match` ✓ | ✅ | ✅ | Done |
| Lambda | `lambda x: x` | `\x: x` ✓ | ✅ | ✅ | Done |
| In operator | `x in items` | `x in items` ✓ | ✅ | ✅ | Done |
| List comprehension | `[x for x in y]` | `[x for x in y]` | ✅ | ✅ | High |
| Dict comprehension | `{k:v for ...}` | `{k:v for ...}` | ✅ | ✅ | High |
| Unpacking | `a, b = b, a` | `a, b = b, a` | ✅ | ✅ | High |
| Slicing | `x[1:3]` | `x[1:3]` | ✅ | ✅ | High |
| Negative index | `x[-1]` | `x[-1]` | ✅ | ✅ | High |
| Context manager | `with x as y:` | `with x as y:` | ✅ | ✅ | High |
| Chained compare | `0 < x < 10` | `0 < x < 10` | ✅ | ✅ | Medium |
| Spread | `[*a, *b]` | `[*a, *b]` | ✅ | ✅ | Medium |
| Decorators | `@deco` | `@deco` (active) | ✅ | ⚠️ | Medium |
| Attributes | N/A | `#[attr]` (passive) | ✅ | ✅ | Medium |
| Walrus | `:=` | `let` in expr | ⚠️ | ⚠️ | Low |
| For-else | `for...else` | `for...else` | ✅ | ✅ | Low |
| Truthiness | `if items:` | Explicit only | ❌ | ❌ | Rejected |

---

## Implementation Order

### Phase 1: Core Comprehensions
1. List comprehension `[x for x in items]`
2. Dict comprehension `{k: v for ...}`
3. Slicing `items[1:3]`
4. Negative indexing `items[-1]`

### Phase 2: Unpacking & Safety
1. Tuple unpacking `a, b = b, a`
2. Rest unpacking `first, *rest = items`
3. Context managers `with resource as r:`

### Phase 3: Convenience
1. Chained comparisons `0 < x < 10`
2. Spread operators `[*a, *b]`
3. Decorators `@decorator`

### Phase 4: Optional
1. Assignment expressions (walrus)
2. For-else

---

## Grammar Changes Required

```ebnf
(* Additions to Simple grammar *)

(* Comprehensions *)
list_comprehension = '[' expr 'for' pattern 'in' expr ['if' expr] ']' ;
dict_comprehension = '{' expr ':' expr 'for' pattern 'in' expr ['if' expr] '}' ;

(* Slicing *)
slice = [expr] ':' [expr] [':' [expr]] ;
index_or_slice = expr '[' (slice | expr) ']' ;

(* Unpacking *)
unpack_pattern = pattern {',' pattern} [',' '*' IDENT] ;
unpack_assignment = unpack_pattern '=' expr ;

(* Context manager *)
with_stmt = 'with' expr 'as' IDENT ':' block ;

(* Chained comparison - handled in semantic analysis *)
comparison = expr (comp_op expr)+ ;

(* Spread *)
spread_element = '*' expr ;
dict_spread = '**' expr ;

(* Decorators *)
decorator = '@' expr NEWLINE ;
decorated_def = {decorator} (fn_def | class_def) ;
```

All additions maintain LL(1) parseability.
