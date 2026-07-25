# Simple Language Primitives Analysis
## Comparison with Ruby and Python Utility Functions

**Last updated**: 2026-01-24

Based on the Simple language specification and README, this analysis identifies missing utility functions compared to Ruby and Python's rich standard libraries, and evaluates whether Simple follows Ruby's "simple and short functions" philosophy.

**Naming Convention**: Simple uses two patterns for predicates:
1. **Existence checks → Use `.?` operator**: `opt.?`, `list.?`, `result.ok.?` (replaces `is_some`, `is_none`, `is_empty`, `is_ok`, `is_err`)
2. **Value predicates → Keep `is_` prefix**: `n.is_even`, `n.is_positive`, `f.is_nan` (these check properties of the value, not existence)

**Status Summary**: After codebase audit (2026-01-24), **~80% of suggested methods already exist**. The `.?` operator and no-paren methods are now implemented, enabling Ruby-like brevity.

---

## Implemented: Ruby-like Brevity Features

### Feature 1: Existence Operator `.?` (Implemented)

The `.?` postfix operator checks if a value is **present** (not nil AND not empty):

| Value | `.?` Result | Reason |
|-------|-------------|--------|
| `nil` / `None` | `false` | no value |
| `Some(x)` | `true` | has value |
| `[]` (empty list) | `false` | empty |
| `[1, 2]` | `true` | has elements |
| `{}` (empty dict) | `false` | empty |
| `{"a": 1}` | `true` | has keys |
| `""` (empty string) | `false` | empty |
| `"hello"` | `true` | has chars |
| `0` | `true` | is a value |
| `false` | `true` | is a value |

```simple
# Optional check
user.?                      # true if user is Some (not nil)
user.parent.?               # true if parent exists

# Collection check
user.children.?             # true if children list is non-empty
user.tags.?                 # true if tags set is non-empty

# String check
user.name.?                 # true if name is non-empty string

# Chained
user?.children.?            # user exists AND has children
user?.profile?.email.?      # all exist AND email non-empty
```

### Feature 2: No-Paren Method Calls (Implemented)

Allow omitting `()` for no-argument methods, making them property-like:

```simple
# Current (requires parens)
if list.is_empty():
if num.is_even():
val len = name.len()

# Proposed (parens optional for no-arg methods)
if list.is_empty:
if num.is_even:
val len = name.len

# Chaining without parens
val result = text.trim.lower.split(",")
#                 ^    ^     ^-- has args, needs ()
#                 |    +-- no args, no parens
#                 +-- no args, no parens
```

### Combined: Ruby `?` Methods → Simple Mapping

#### Use `.?` (Existence Check Only)

| Ruby | Simple with `.?` | Notes |
|------|------------------|-------|
| `!x.nil?` | `x.?` | has value |
| `x.nil?` | `not x.?` | is nil |
| `x.present?` | `x.?` | Rails present |
| `!x.blank?` | `x.?` | has content |
| `hash.key?("k")` | `hash["k"].?` | key exists |
| `hash.has_key?("k")` | `hash["k"].?` | key exists |
| `File.exist?(p)` | `File.stat(p).?` | file exists |

#### Use `.?` (Existence/Presence Check)

| Ruby | Simple with `.?` | Notes |
|------|------------------|-------|
| `arr.empty?` | `not arr.?` | Empty = not present |
| `!arr.empty?` | `arr.?` | Has items = present |
| `s.blank?` | `not s.trim.?` | Empty/whitespace = not present |
| `!s.blank?` | `s.trim.?` | Has content = present |
| `arr.any?` (no block) | `arr.?` | Has elements = present |
| `arr.none?` (no block) | `not arr.?` | No elements = not present |

#### Use `is_` Methods (Value Predicates - Keep `is_` Prefix)

| Ruby | Simple (no parens) | Notes |
|------|-------------------|-------|
| `n.zero?` | `n.is_zero` | Value predicate |
| `n.even?` | `n.is_even` | Value predicate |
| `n.odd?` | `n.is_odd` | Value predicate |
| `n.positive?` | `n.is_positive` | Value predicate |
| `n.negative?` | `n.is_negative` | Value predicate |
| `n.finite?` | `n.is_finite` | Value predicate |
| `n.nan?` | `n.is_nan` | Value predicate |
| `n.infinite?` | `n.is_infinite` | Value predicate |
| `f.eof?` | `f.eof` | State predicate |
| `f.closed?` | `f.closed` | State predicate |
| `t.utc?` | `t.utc` | State predicate |
| `t.sunday?` | `t.sunday` | Weekday check |
| `r.exclude_end?` | `r.exclusive` | Range property |
| `thread.alive?` | `thread.alive` | State predicate |
| `arr.one?` | `arr.len == 1` | Use comparison |
| `arr.many?` | `arr.len > 1` | Use comparison |

#### Need Parens (Has Arguments)

| Ruby | Simple (needs parens) | Notes |
|------|----------------------|-------|
| `s.include?("x")` | `s.contains("x")` | has arg |
| `s.start_with?("x")` | `s.starts_with("x")` | has arg |
| `s.end_with?("x")` | `s.ends_with("x")` | has arg |
| `s.match?(re)` | `s.matches(re)` | has arg |
| `n.between?(a, b)` | `n.between(a, b)` | has args |
| `arr.any? { }` | `arr.any(\x: ...)` | has block |
| `arr.all? { }` | `arr.all(\x: ...)` | has block |
| `set.subset?(o)` | `set.subset(o)` | has arg |
| `set.disjoint?(o)` | `set.disjoint(o)` | has arg |
| `obj.is_a?(T)` | `obj is T` | use operator |
| `obj.respond_to?(:m)` | `obj.has_method("m")` | has arg |

### Complete Ruby `?` Method Reference

#### Core Object / Nil (Use `.?`)

| Ruby | Simple | Notes |
|------|--------|-------|
| `x.nil?` | `not x.?` | Existence check |
| `!x.nil?` | `x.?` | Existence check |
| `x.present?` | `x.?` | Existence check |
| `x.blank?` | `not x.?` | Existence check (for strings: `not x.trim.?`) |
| `defined?(x)` | `x.?` | Existence check |
| `x.frozen?` | `x.frozen` | State predicate (keep as method) |

#### Numeric (Keep `is_` - Value Predicates)

| Ruby | Simple | Notes |
|------|--------|-------|
| `n.zero?` | `n.is_zero` | Value predicate |
| `n.nonzero?` | `not n.is_zero` | Value predicate |
| `n.positive?` | `n.is_positive` | Value predicate |
| `n.negative?` | `n.is_negative` | Value predicate |
| `n.even?` | `n.is_even` | Value predicate |
| `n.odd?` | `n.is_odd` | Value predicate |
| `n.integer?` | `n is i64` | Use type check operator |
| `n.finite?` | `n.is_finite` | Value predicate |
| `n.infinite?` | `n.is_infinite` | Value predicate |
| `n.nan?` | `n.is_nan` | Value predicate |
| `n.between?(a,b)` | `a <= n and n <= b` | Use chained comparison |

#### String (Use `.?` for Empty Checks)

| Ruby | Simple | Notes |
|------|--------|-------|
| `s.empty?` | `not s.?` | Existence check |
| `!s.empty?` | `s.?` | Existence check |
| `s.blank?` | `not s.trim.?` | Existence check (after trim) |
| `!s.blank?` | `s.trim.?` | Existence check (after trim) |
| `s.ascii_only?` | `s.is_ascii` | Value predicate (keep `is_`) |
| `s.include?(x)` | `s.contains(x)` | Needs parens |
| `s.start_with?(x)` | `s.starts_with(x)` | Needs parens |
| `s.end_with?(x)` | `s.ends_with(x)` | Needs parens |
| `s.match?(re)` | `s.matches(re)` | Needs parens |

#### Array / Enumerable (Use `.?` for Empty Checks)

| Ruby | Simple | Notes |
|------|--------|-------|
| `a.empty?` | `not a.?` | Existence check |
| `!a.empty?` | `a.?` | Existence check |
| `a.any?` (no block) | `a.?` | Existence check |
| `a.any? { }` | `a.any(\x: ...)` | Needs parens (with predicate) |
| `a.all? { }` | `a.all(\x: ...)` | Needs parens |
| `a.none?` (no block) | `not a.?` | Existence check |
| `a.one?` | `a.len == 1` | Use comparison |
| `a.many?` | `a.len > 1` | Use comparison |
| `a.include?(x)` | `a.contains(x)` | Needs parens |

#### Hash / Dict (Use `.?` for Empty/Key Checks)

| Ruby | Simple | Notes |
|------|--------|-------|
| `h.empty?` | `not h.?` | Existence check |
| `!h.empty?` | `h.?` | Existence check |
| `h.any?` (no block) | `h.?` | Existence check |
| `h.key?(k)` | `h[k].?` | Existence check |
| `h.has_key?(k)` | `h[k].?` | Existence check |
| `h.value?(v)` | `h.has_value(v)` | Needs parens |

#### Set (Use `.?` for Empty Checks)

| Ruby | Simple | Notes |
|------|--------|-------|
| `s.empty?` | `not s.?` | Existence check |
| `!s.empty?` | `s.?` | Existence check |
| `s.include?(x)` | `s.contains(x)` | Needs parens |
| `s.subset?(o)` | `s.is_subset(o)` | Needs parens (value predicate) |
| `s.superset?(o)` | `s.is_superset(o)` | Needs parens (value predicate) |
| `s.disjoint?(o)` | `s.is_disjoint(o)` | Needs parens (value predicate) |

#### File / IO (Mixed)

| Ruby | Simple | Notes |
|------|--------|-------|
| `File.exist?(p)` | `file_exist(p)` | Function (existence check) |
| `File.file?(p)` | `is_file(p)` | Value predicate (keep `is_`) |
| `File.directory?(p)` | `is_dir(p)` | Value predicate (keep `is_`) |
| `f.eof?` | `f.eof` | State predicate |
| `f.closed?` | `f.closed` | State predicate |
| `f.tty?` | `f.tty` | State predicate |

#### Time / Date

| Ruby | Simple | Type |
|------|--------|------|
| `t.dst?` | `t.dst` | no-paren |
| `t.utc?` | `t.utc` | no-paren |
| `t.sunday?` | `t.sunday` | no-paren |
| `t.monday?` | `t.monday` | no-paren |
| `t.tuesday?` | `t.tuesday` | no-paren |
| `t.wednesday?` | `t.wednesday` | no-paren |
| `t.thursday?` | `t.thursday` | no-paren |
| `t.friday?` | `t.friday` | no-paren |
| `t.saturday?` | `t.saturday` | no-paren |
| `d.leap?` | `d.leap_year` | no-paren |

#### Range

| Ruby | Simple | Type |
|------|--------|------|
| `r.cover?(x)` | `r.covers(x)` | needs parens |
| `r.include?(x)` | `r.contains(x)` | needs parens |
| `r.exclude_end?` | `r.exclusive` | no-paren |

#### Type Checking

| Ruby | Simple | Type |
|------|--------|------|
| `x.is_a?(T)` | `x is T` | operator |
| `x.kind_of?(T)` | `x is T` | operator |
| `x.respond_to?(:m)` | `x.has_method("m")` | needs parens |

### Summary: Pattern Count

| Pattern | Count | Simple Syntax | Examples |
|---------|-------|---------------|----------|
| **Use `.?`** | ~15 | `x.?` | `opt.?`, `list.?`, `dict["k"].?`, `result.ok.?` |
| **Keep `is_` methods** | ~20 | `x.is_method` | `n.is_even`, `n.is_positive`, `f.is_nan` |
| **No-paren methods** | ~25 | `x.method` | `list.first`, `s.trim`, `s.upper` |
| **Need parens (args)** | ~25 | `x.method(arg)` | `s.contains(x)`, `a.any(\x: ...)` |
| **Use operators** | ~5 | `x is T`, `a <= n <= b` | Type check, chained comparison |

### Example: Ruby vs Simple

```ruby
# Ruby
def process(user)
  return nil if user.nil?
  return nil if user.email.nil? || user.email.empty?
  return nil unless user.active?
  user.email.downcase.strip
end
```

```simple
# Simple (with implemented features)
fn process(user):
    if not user.?:                    # nil check via .?
        return nil
    if not user!.email.?:             # existence + empty via .?
        return nil
    if not user!.active:              # bool property, no parens
        return nil
    user!.email!.lower.trim           # no parens for no-arg methods

# Even more concise with guard clauses
fn process(user):
    return nil if not user.?
    return nil if not user!.email.?
    return nil if not user!.active
    user!.email!.lower.trim
```

---

## Quick Status: Grammar Features (Verified 2026-01-24)

| Feature | Status | Example |
|---------|--------|---------|
| Safe navigation `?.` | ✅ Implemented | `user?.address?.city` |
| Null coalescing `??` | ✅ Implemented | `name ?? "default"` |
| Slice syntax | ✅ Implemented | `lst[1:5]`, `lst[::2]`, `lst[1:10:2]` |
| Negative indexing | ✅ Implemented | `lst[-1]`, `lst[-2]` |
| List comprehension | ✅ Implemented | `[x*2 for x in lst if x > 0]` |
| Dict comprehension | ✅ Implemented | `{k: v for k, v in items}` |
| Destructuring | ✅ Implemented | `let (a, b) = tuple` |
| Pattern guards | ✅ Implemented | `case n if n > 0:` |
| With statement | ✅ Implemented | `with File.open(p) as f:` |
| Chained comparison | ✅ Implemented | `0 < x < 10` |
| Spread operator | ✅ Implemented | `[...a, ...b]` |
| Named arguments | ✅ Implemented | `foo(x: 1, y: 2)` |
| Default parameters | ✅ Implemented | `fn foo(x = 0)` |
| Raw strings | ✅ Implemented | `r"no\escape"` |
| Ranges | ✅ Implemented | `1..10`, `1..=10` |
| **Existence `.?`** | ✅ Implemented | `user.?`, `list.?`, `dict["k"].?` |
| **No-paren methods** | ✅ Implemented | `list.first`, `s.upper`, `s.trim` |
| Byte strings | ❌ Not implemented | `b"bytes"` |
| For-else | ❌ Not implemented | `for x in lst: else:` |
| Pipeline `\|>` | ❌ Not implemented | Use method chaining |

**Key finding**: Most grammar features are already implemented. Main gaps are in **stdlib methods** (string, number, collection utilities).

**Implemented features** (see above section):
- `.?` existence operator: checks non-nil AND non-empty
- No-paren method calls: `list.first`, `s.upper`, `s.trim` without `()`

---

## Key Insight: Why Ruby Feels "Short"

The reason Ruby feels "small but powerful" is that core objects expose a **dense, orthogonal set of methods** and share a **common iteration surface** (Enumerable). The largest determinant of whether Simple will feel "Ruby-short" is not syntax—it is:

1. **A unified iteration/pipeline API** across all collections
2. **Consistent naming** across primitives and collections
3. **Everything is chainable** (or pipeline-friendly)

---

## 1. String Type

### Currently Documented in Simple
From spec: `String` supports concatenation, slicing, searching, formatting, and string interpolation (`"Hello, {name}!"`).

### Capability Clusters (Ruby/Python Baseline)

| Cluster | Expected Methods | Simple Status |
|---------|------------------|---------------|
| **Basic** | `len`, `is_empty`, indexing/slicing | ⚠️ Partial |
| **Search** | `contains`, `find`, `rfind`, `starts_with`, `ends_with`, `count` | ⚠️ "searching" only |
| **Transform** | `lower`, `upper`, `capitalize`, `trim`, `repeat` | ❌ Missing |
| **Split/Join** | `split(sep, limit)`, `join(iter)` | ❌ Missing |
| **Replace** | `replace(old, new, count)`, regex `sub`/`gsub` | ❌ Missing |
| **Encoding** | UTF-8 default, `bytes` view | ❌ Not specified |
| **Formatting** | interpolation, `format()` | ✅ Interpolation exists |

### Functions Status - Consolidated Table

**Source**: `src/rust/compiler/src/interpreter_method/string.rs`

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `len` | `len` | ✅ Same | Line 20 |
| `empty` | `is_empty` | ✅ Longer | Line 22 - uses `is_` prefix |
| `trim` | `trim`, `trimmed`, `strip` | ✅ Same + aliases | Line 91 |
| `ltrim` | `trim_start`, `trim_left` | ✅ Longer | Aliases available |
| `rtrim` | `trim_end`, `trim_right` | ✅ Longer | Aliases available |
| `up` | `upper`, `to_upper`, `to_uppercase` | ✅ Longer | Line 50 - uses `upper` not `up` |
| `down` | `lower`, `to_lower`, `to_lowercase` | ✅ Longer | Line 51 - uses `lower` not `down` |
| `capitalize` | `capitalize` | ✅ Same | Implemented |
| `rev` | `reversed`, `reverse` | ✅ Same | Lines 144, 283 |
| `split` | `split` | ✅ Same | Line 188 |
| `join` | `join` | ✅ Same | On array type |
| `replace` | `replace`, `replace_first` | ✅ Same | Lines 255, 260 |
| `find` | `find`, `find_str`, `index_of` | ✅ Same | Line 43 |
| `rfind` | `last_index_of`, `rfind` | ✅ Same | Implemented |
| `contains` | `contains` | ✅ Same | Line 31 |
| `starts_with` | `starts_with` | ✅ Same | Line 35 |
| `ends_with` | `ends_with` | ✅ Same | Line 39 |
| `count` | `count` | ✅ Same | Implemented |
| `repeat` | `repeat` | ✅ Same | Implemented |
| `chars` | `chars` | ✅ Same | Line 23 |
| `lines` | `lines`, `split_lines` | ✅ Same | Line 193 |
| `bytes` | `bytes` | ✅ Same | Implemented |
| `to_int` | `to_int`, `parse_int` | ✅ Same | Lines 293, 305 |
| `to_float` | `to_float`, `parse_float` | ✅ Same | Lines 299, 311 |
| `is_digit` | `is_numeric` | ✅ Same | Implemented |
| `is_alpha` | `is_alpha` | ✅ Same | Implemented |
| `center` | `center` | ✅ Same | Implemented |
| `pad_left` | `pad_left`, `pad_start` | ✅ Same | Implemented |
| `pad_right` | `pad_right`, `pad_end` | ✅ Same | Implemented |

**Additional String Methods** (not in original doc):
- `capitalize`, `swapcase`, `title`, `titlecase`
- `removeprefix`, `removesuffix`, `chomp`, `squeeze`
- `sorted`, `taken`, `dropped`, `appended`, `prepended`
- `push`, `push_str`, `pop`, `clear`
- `partition`, `rpartition`, `slice`, `substring`
- `char_at`, `at`, `ord`, `codepoint`, `zfill`
- `is_alphanumeric`, `is_whitespace`, `char_count`

### Current Simple String API (Implemented)
```simple
# Existence check with .?
s.?               # true if non-empty string ✅
not s.?           # true if empty (replaces is_empty) ✅
s.trim.?          # true if non-empty after trim ✅

# Methods (no-paren for no-arg)
s.len             # length ✅
s.trim            # strip whitespace ✅
s.upper           # uppercase ✅
s.lower           # lowercase ✅
s.reverse         # reverse ✅
s.split(",")      # split by separator ✅
s.replace("a", "b")   # replace all ✅
s.contains("x")   # substring check ✅
s.starts_with("http") # ✅
s.ends_with(".txt")   # ✅

# Chainable - works today
name.trim.lower.split(",").map(\x: x.trim)
```

---

## 2. Number Types (Int, Float)

### Currently Documented in Simple
From spec: `Int`, `Float`, `Bool`, `Char` with math functions (`sqrt`, `sin`, etc.) in a `Math` module or as methods.

### Capability Clusters (Ruby/Python Baseline)

| Cluster | Expected Methods | Simple Status |
|---------|------------------|---------------|
| **Conversions** | `to_int`, `to_float`, `to_string(base)`, parse | ❌ Missing |
| **Rounding** | `floor`, `ceil`, `round(digits)`, `trunc` | ❌ Missing |
| **Math helpers** | `abs`, `clamp`, `sign`, `pow`, `sqrt`, `log`, `exp` | ⚠️ Partial (Math module) |
| **Div semantics** | `div`, `mod`, `divmod` | ❌ Missing |
| **Bit ops** | `<<`, `>>`, `&`, `\|`, `^`, `bit_len`, `popcount` | ❌ Not specified |
| **Predicates** | `is_nan`, `is_inf`, `is_even`, `is_odd`, `is_zero` | ❌ Missing |

### Functions Status - Consolidated Table

**Source**: `src/rust/compiler/src/interpreter_method/primitives.rs`

#### Int Methods (Lines 10-211)

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `abs` | `abs` | ✅ Same | Line 21 |
| `sign` | `sign`, `signum` | ✅ Same | Line 22 |
| `clamp` | `clamp` | ✅ Same | Line 30 |
| `even` | `is_even` | ✅ Longer | Line 26 - uses `is_` prefix |
| `odd` | `is_odd` | ✅ Longer | Line 27 - uses `is_` prefix |
| `positive` | `is_positive` | ✅ Longer | Line 23 - uses `is_` prefix |
| `negative` | `is_negative` | ✅ Longer | Line 24 - uses `is_` prefix |
| `zero` | `is_zero` | ✅ Longer | Line 25 - uses `is_` prefix |
| `to_string` | `to_string` | ✅ Same | Line 29 |
| `to_float` | `to_float` | ✅ Same | Implemented |
| `pow` | `pow` | ✅ Same | Implemented |
| `bit_len` | `bit_length` | ✅ Same | Implemented |
| `popcount` | `bit_count`, `count_ones` | ✅ Same | Implemented |
| `divmod` | ❌ | ❌ Missing | Not implemented |
| `between` | ❌ | ❌ Missing | Not implemented |

**Additional Int Methods**: `min`, `max`, `leading_zeros`, `trailing_zeros`, `to_hex`, `to_bin`, `to_oct`, `times`, `up_to`, `down_to`, `gcd`, `lcm`, `digits`, `chr`

#### Float Methods (Lines 214-401)

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `abs` | `abs` | ✅ Same | Line 225 |
| `floor` | `floor` | ✅ Same | Line 235 |
| `ceil` | `ceil` | ✅ Same | Line 236 |
| `round` | `round` | ✅ Same | Line 237 |
| `trunc` | `trunc`, `truncate` | ✅ Same | Implemented |
| `clamp` | `clamp` | ✅ Same | Line 256 |
| `sign` | `sign`, `signum` | ✅ Same | Line 226 |
| `positive` | `is_positive` | ✅ Longer | Line 227 - uses `is_` prefix |
| `negative` | `is_negative` | ✅ Longer | Line 228 - uses `is_` prefix |
| `zero` | `is_zero` | ✅ Longer | Line 229 - uses `is_` prefix |
| `sqrt` | `sqrt` | ✅ Same | Implemented |
| `is_nan` | `is_nan` | ✅ Same | Implemented |
| `is_inf` | `is_infinite` | ✅ Same | Implemented |
| `to_string` | `to_string` | ✅ Same | Line 234 |
| `to_int` | `to_int` | ✅ Same | Implemented |

**Additional Float Methods**: `fract`, `cbrt`, `exp`, `exp2`, `ln`, `log2`, `log10`, `log`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`, `tanh`, `hypot`, `pow`, `powf`, `powi`, `round_to`, `is_finite`, `is_integer`, `as_integer_ratio`, `to_degrees`, `to_radians`

### Inconsistency Traps to Avoid
- **`mod` sign rules**: Python's `%` is always non-negative; C/Ruby can be negative. Pick one and document.
- **`round` ties**: Ties-to-even vs ties-away-from-zero. Pick one.

### Current Simple Number API (Implemented)
```simple
# Numbers always exist, so n.? is always true
n.?               # always true (numbers are values) ✅

# Math methods (no-paren for no-arg)
n.abs             # ✅
n.floor           # ✅
n.ceil            # ✅
n.round(2)        # round to 2 decimal places ✅ (round_to)
n.clamp(0, 100)   # clamp to range ✅

# Value predicates - keep is_ prefix (these check properties, not existence)
n.is_even         # checks if value is even ✅
n.is_odd          # checks if value is odd ✅
n.is_positive     # checks if n > 0 ✅
n.is_negative     # checks if n < 0 ✅
n.is_zero         # checks if n == 0 ✅
f.is_nan          # checks if float is NaN ✅
f.is_infinite     # checks if float is infinite ✅

# Chainable - works today
x.abs.clamp(0, 10).to_string
```

### Naming Strategy: `.?` vs `is_`

The `.?` operator now handles **existence/presence checks**, so many `is_` methods are no longer needed:

| Use `.?` (Existence) | Keep `is_` (Value Predicate) |
|---------------------|------------------------------|
| `opt.?` replaces `is_some()` | `n.is_even` (checks value property) |
| `not opt.?` replaces `is_none()` | `n.is_odd` (checks value property) |
| `list.?` replaces `not is_empty()` | `n.is_positive` (checks value property) |
| `not list.?` replaces `is_empty()` | `n.is_negative` (checks value property) |
| `result.ok.?` replaces `is_ok()` | `f.is_nan` (checks value property) |
| `result.err.?` replaces `is_err()` | `f.is_infinite` (checks value property) |

**Key insight**: `.?` is for "does this exist/have content?" while `is_` is for "what property does this value have?"

---

## 3. Collections (Array/Vec/List, Map/Dict, Set)

### Currently Documented in Simple
From spec: `List<T>`, `Vec<T>`, `Dict<K,V>`, `Set<T>` with `map`, `filter`, `reduce`, `Iterable` trait.

### Critical: Enumerable-Equivalent Trait

**This is the #1 determinant of Ruby-like feel.** Ruby's `Enumerable` mixin provides 50+ methods to any collection. Simple's `Iterable` trait must provide:

| Method | Description | Priority |
|--------|-------------|----------|
| `map` | Transform each element | ✅ Exists |
| `filter` | Keep matching elements | ✅ Exists |
| `reduce` / `fold` | Aggregate to single value | ✅ Exists |
| `any` | True if any match predicate | ❌ **Critical** |
| `all` | True if all match predicate | ❌ **Critical** |
| `find` | First matching element | ❌ **Critical** |
| `find_index` | Index of first match | ❌ |
| `zip` | Combine with another iterable | ❌ **Critical** |
| `enumerate` | Pairs of (index, value) | ❌ **Critical** |
| `group_by` | Group by key function | ❌ **Critical** |
| `partition` | Split by predicate | ❌ |
| `flat_map` | Map then flatten | ❌ |
| `take` | First n elements | ❌ |
| `drop` | Skip first n elements | ❌ |
| `take_while` | Take while predicate true | ❌ |
| `drop_while` | Skip while predicate true | ❌ |
| `chunk` | Group consecutive | ❌ |
| `each_slice` | Iterate in chunks of n | ❌ |
| `each_cons` | Sliding window of n | ❌ |

### Vec/Array - Functions Status

**Source**: `src/rust/compiler/src/interpreter_method/collections.rs` (Lines 14-564)

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `len` | `len` | ✅ Same | Line 25 |
| `empty` | `is_empty` | ✅ Longer | Line 26 - uses `is_` prefix |
| `push` | `push`, `append` | ✅ Same | Line 37 |
| `pop` | `pop` | ✅ Same | Line 43 |
| `insert` | `insert` | ✅ Same | Implemented |
| `remove_at` | `remove` | ✅ Same | Implemented |
| `clear` | `clear` | ✅ Same | Implemented |
| `first` | `first` | ✅ Same | Line 27 |
| `last` | `last` | ✅ Same | Line 28 |
| `take` | `take` | ✅ Same | Line 293 |
| `drop` | `skip`, `drop` | ✅ Same | Line 297 |
| `slice` | `slice` | ✅ Same | Implemented |
| `concat` | `concat`, `extend` | ✅ Same | Implemented |
| `rev` | `reverse` | ✅ Longer | Line 90 |
| `sort` | `sort` | ✅ Same | Line 212 |
| `sort_by` | Partial | ⚠️ Partial | Use `map` + `sort` |
| `uniq` | `unique`, `distinct` | ✅ Same | Line 357 |
| `flat` | `flatten` | ✅ Same | Implemented |
| `compact` | `compact` | ✅ Same | Implemented |
| `shuffle` | `shuffle` | ✅ Same | Implemented |
| `sample` | `sample` | ✅ Same | Implemented |
| `min` | `min` | ✅ Same | Line 368 |
| `max` | `max` | ✅ Same | Line 377 |
| `sum` | `sum` | ✅ Same | Line 190 |
| `contains` | `contains` | ✅ Same | Line 33 |
| `index` | `index_of` | ✅ Same | Implemented |
| `count` | `count` | ✅ Same | Implemented |
| `join` | `join` | ✅ Same | Implemented |

**Opinion - Consider Shorter Aliases**:
| Current | Shorter | Notes |
|---------|---------|-------|
| `is_empty` | `empty` | Common operation |
| `reverse` | `rev` | Ruby uses `reverse`, but `rev` is shorter |
| `unique` | `uniq` | Ruby uses `uniq` |

### Dict/Map - Functions Status

**Source**: `src/rust/compiler/src/interpreter_method/collections.rs` (Lines 666-866) + `simple/std_lib/src/map.spl`

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `len` | `len` | ✅ Same | Line 677 |
| `empty` | `is_empty` | ✅ Longer | Line 678 - uses `is_` prefix |
| `get` | `get` | ✅ Same | Line 683 |
| `set` | `set`, `insert` | ✅ Same | Implemented |
| `remove` | `remove`, `delete` | ✅ Same | Implemented |
| `contains_key` | `contains_key`, `contains` | ✅ Same | Line 679 |
| `contains_value` | ❌ | ❌ Missing | Not implemented |
| `keys` | `keys` | ✅ Same | Line 687 |
| `values` | `values` | ✅ Same | Line 691 |
| `items` | `entries`, `items` | ✅ Same | Line 739 |
| `merge` | `merge`, `extend` | ✅ Same | Line 708 |
| `invert` | ❌ | ❌ Missing | Not implemented |
| `select` | `filter` | ✅ Same | Implemented in map.spl |
| `transform_keys` | ❌ | ❌ Missing | Not implemented |
| `transform_values` | `map_values` | ✅ Same | Implemented in map.spl |
| `dig` | `dig` | ✅ Same | Implemented (nested navigation) |

**Additional Dict Methods** (from map.spl): `get_or_default`, `insert_if_absent`, `update`, `for_each`, `clone`, `clear`, `compact`, `fetch`, `setdefault`

**Opinion - Consider Shorter Aliases**:
| Current | Shorter | Notes |
|---------|---------|-------|
| `is_empty` | `empty` | Common operation |
| `contains_key` | `has` | Ruby uses `has_key?`, `has` is shorter |

### Set - Functions Status

**Source**: `simple/std_lib/src/set.spl`

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `len` | `len` | ✅ Same | Line 38 |
| `empty` | `is_empty` | ✅ Longer | Line 49 - uses `is_` prefix |
| `add` | `insert` | ✅ Different | Line 61 - uses `insert` (Rust style) |
| `remove` | `remove` | ✅ Same | Line 91 |
| `contains` | `contains` | ✅ Same | Line 76 |
| `union` | `union` | ✅ Same | Line 139 |
| `intersect` | `intersection` | ✅ Longer | Line 156 |
| `diff` | `difference` | ✅ Longer | Line 174 |
| `symmetric_diff` | `symmetric_difference` | ✅ Longer | Implemented |
| `subset` | `is_subset` | ✅ Longer | Uses `is_` prefix |
| `superset` | `is_superset` | ✅ Longer | Uses `is_` prefix |

**Additional Set Methods**: `is_disjoint`, `filter`, `map`, `any`, `all`, `clone`, `extend`, `clear`, `to_list`, `for_each`

**Opinion - Consider Shorter Aliases**:
| Current | Shorter | Notes |
|---------|---------|-------|
| `is_empty` | `empty` | Common operation |
| `insert` | `add` | Ruby/Python use `add` |
| `intersection` | `intersect` | 5 chars shorter |
| `difference` | `diff` | 7 chars shorter |
| `symmetric_difference` | `sym_diff` | Much shorter |
| `is_subset` | `subset` | Drop `is_` prefix |
| `is_superset` | `superset` | Drop `is_` prefix |

### Current Simple Collections API (Implemented)
```simple
# Vec - existence check with .?
v.?               # true if non-empty (replaces not is_empty) ✅
not v.?           # true if empty (replaces is_empty) ✅
v.first.?         # true if has first element ✅
v.last.?          # true if has last element ✅

# Vec - methods (no-paren for no-arg)
v.len             # ✅
v.first           # ✅ (no parens needed)
v.last            # ✅ (no parens needed)
v.push(x)         # ✅
v.pop             # ✅
v.take(3)         # ✅
v.drop(3)         # ✅ (also: skip)
v.reverse         # ✅ (no parens needed)
v.sort            # ✅
v.unique          # ✅ (also: distinct)
v.contains(x)     # ✅

# Iteration pipeline - WORKS TODAY
data
    .filter(\x: x > 0)
    .map(\x: x * 2)
    .group_by(\x: x % 10)
    .entries
    .sort

# Dict - existence check with .?
d.?               # true if non-empty ✅
d["key"].?        # true if key exists ✅

# Dict - methods
d.get("key")          # ✅
d.get_or_default("key", default)  # ✅
d.keys                # ✅
d.values              # ✅
d.entries             # ✅ (also: items)
d.merge(other)        # ✅

# Boolean aggregation - WORKS TODAY
lst.any(\x: x > 10)   # ✅
lst.all(\x: x > 0)    # ✅
lst.find(\x: x > 0)   # ✅ (returns Option)
```

---

## 4. File I/O and Paths

### Currently Documented in Simple
From spec: `File` class or functions for read/write, streams, binary/text modes.

### Critical: One-Liner Convenience APIs

The #1 reason Python scripts feel short is convenience APIs. Simple needs these for "Ruby feel":

```simple
# One-liner file operations (CRITICAL for Ruby/Python feel)
content = File.read("data.txt")           # Read entire file
File.write("out.txt", content)            # Write entire file
lines = File.lines("data.txt")            # Read as line array

# Safe close with block (Ruby/Python style)
File.open("data.txt") \f:
    data = f.read
    # auto-closed after block
```

### Capability Clusters (Ruby/Python Baseline)

| Cluster | Expected Methods | Simple Status |
|---------|------------------|---------------|
| **File open** | `File.open(path, mode)`, safe-close | ❌ Not documented |
| **Convenience** | `read`, `write`, `read_lines`, `write_lines` | ❌ Not documented |
| **Line iteration** | `each_line`, line iterator | ❌ Not documented |
| **Path ops** | `join`, `dirname`, `basename`, `ext`, `normalize` | ❌ Not documented |
| **Existence** | `exists`, `is_dir`, `is_file` | ❌ Not documented |
| **Directory** | `list_dir`, `mkdir`, `rmdir`, `glob` | ❌ Not documented |
| **Metadata** | `stat`, `size`, `mtime` | ❌ Not documented |

### Functions Status - Consolidated Table

**Source**: `src/lib/std/src/infra/file_io.spl` (Full implementation exists!)

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `File.read` | `read_file(path)` | ✅ Longer | Line 37 - returns `Result<text, text>` |
| `File.write` | `write_file(path, content)` | ✅ Longer | Line 56 - returns `Result<(), text>` |
| `File.lines` | ❌ | ❌ Missing | Use `read_file(p).split("\n")` |
| `File.append` | ❌ | ❌ Missing | Not implemented |
| `File.read_bytes` | ❌ | ❌ Missing | Not implemented |
| `File.write_bytes` | ❌ | ❌ Missing | Not implemented |
| `File.exists` | `file_exist(path)` | ✅ Same | Line 15 - uses `file_exist` not `file_exists` |
| `File.is_file` | `is_file(path)` | ✅ Same | Line 250 |
| `File.is_dir` | `is_dir(path)` | ✅ Same | Line 254 |
| `File.size` | `file_size(path)` | ✅ Same | Line 22 - returns `Option<i32>` |
| `File.delete` | `remove_file(path)` | ✅ Longer | Line 89 |
| `File.rename` | `rename_file(old, new)` | ✅ Longer | Line 100 |
| `File.copy` | `copy_file(src, dest)` | ✅ Longer | Line 75 |
| `File.move` | ❌ | ❌ Missing | Use `copy_file` + `remove_file` |
| `f.read` | `rt_file_read_text` | ⚠️ FFI only | Low-level FFI |
| `f.write` | `rt_file_write_text` | ⚠️ FFI only | Low-level FFI |
| `f.seek` | ❌ | ❌ Missing | Not implemented |
| `f.tell` | ❌ | ❌ Missing | Not implemented |
| `f.flush` | ❌ | ❌ Missing | Not implemented |
| `f.close` | `close_file(fd)` | ✅ Same | Line 238 |
| `f.eof` | ❌ | ❌ Missing | Not implemented |

**Opinion - Consider Shorter Names**:
| Current | Shorter | Notes |
|---------|---------|-------|
| `read_file` | `File.read` | Class method style |
| `write_file` | `File.write` | Class method style |
| `file_exist` | `File.exists` | Fix typo: `exist` → `exists` |
| `remove_file` | `File.delete` | Ruby style |
| `rename_file` | `File.rename` | Ruby style |
| `copy_file` | `File.copy` | Ruby style |

### Path Module - Functions Status

**Source**: `src/lib/std/src/infra/file_io.spl` (Lines 169-207)

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `Path.join` | `join_path(parts)` | ✅ Longer | Line 260 - takes `List<text>` |
| `Path.dirname` | `dirname(path)` | ✅ Same | Line 184 |
| `Path.basename` | `basename(path)` | ✅ Same | Line 177 |
| `Path.ext` | `extension(path)` | ✅ Longer | Line 191 |
| `Path.stem` | ❌ | ❌ Missing | Not implemented |
| `Path.normalize` | `canonicalize(path)` | ✅ Longer | Line 111 |
| `Path.absolute` | `absolute_path(path)` | ✅ Longer | Line 198 |
| `Path.relative` | ❌ | ❌ Missing | Not implemented |
| `Path.parent` | `dirname(path)` | ✅ Same | Same as dirname |
| `Path.separator` | `path_separator()` | ✅ Same | Line 205 |
| `Path.split` | `split_path(path)` | ✅ Same | Line 265 |

**Opinion - Consider Shorter Names**:
| Current | Shorter | Notes |
|---------|---------|-------|
| `join_path` | `Path.join` | Class method style |
| `extension` | `ext` | 6 chars shorter |
| `absolute_path` | `Path.abs` | Much shorter |
| `canonicalize` | `Path.canon` | Shorter |
| `path_separator` | `Path.sep` | Much shorter |

### Directory Module - Functions Status

**Source**: `src/lib/std/src/infra/file_io.spl` (Lines 114-167)

| Suggested | Actual Name | Status | Notes |
|-----------|-------------|--------|-------|
| `Dir.list` | `list_dir(path)` | ✅ Longer | Line 133 |
| `Dir.glob` | `glob(pattern)` | ✅ Same | Line 166 |
| `Dir.walk` | ❌ | ❌ Missing | Not implemented |
| `Dir.mkdir` | `create_dir(path)` | ✅ Longer | Line 122 |
| `Dir.mkdir_p` | ❌ | ❌ Missing | Not implemented |
| `Dir.rmdir` | `remove_dir(path)` | ✅ Longer | Line 148 |
| `Dir.rm_rf` | ❌ | ❌ Missing | Not implemented |
| `Dir.exists` | `is_dir(path)` | ✅ Same | Line 254 |
| `Dir.cwd` | ❌ | ❌ Missing | Not implemented |
| `Dir.chdir` | ❌ | ❌ Missing | Not implemented |
| `Dir.find` | `find_files(dir, pattern)` | ✅ Same | Line 159 |

**Opinion - Consider Shorter Names**:
| Current | Shorter | Notes |
|---------|---------|-------|
| `list_dir` | `Dir.list` | Class method style |
| `create_dir` | `Dir.mkdir` | Unix style |
| `remove_dir` | `Dir.rmdir` | Unix style |
| `find_files` | `Dir.find` | Shorter |

### Inconsistency Trap to Avoid
- Splitting "file" and "path" modules requires verbose imports for common tasks
- Solution: Make path operations available both as `Path.join()` and `File.join()`

### Current Simple File/Path API (Implemented)
```simple
use infra.file_io.*

# Result patterns with .?
val result = read_file("data.txt")
if result.ok.?:              # true if read succeeded ✅
    val content = result!
if result.err.?:             # true if read failed ✅
    val error = result.unwrap_err()

# One-liner convenience - WORKS TODAY
content = read_file("data.txt")       # returns Result<text, text> ✅
write_file("out.txt", content)        # returns Result<(), text> ✅
lines = read_file("data.txt")?.split("\n")  # workaround for lines

# Unsafe variants (panics on error)
content = read_file_unsafe("data.txt")  # ✅
write_file_unsafe("out.txt", content)   # ✅

# File/path predicates - keep is_ prefix (value predicates)
file_exist("data.txt")    # ✅ (existence check function)
is_dir("/path")           # ✅ (value predicate: is this a directory?)
is_file("/path")          # ✅ (value predicate: is this a file?)

# Path operations - WORKS TODAY
path = join_path(["dir", "subdir", "file.txt"])  # ✅
dir = dirname(path)       # ✅
name = basename(path)     # ✅
ext = extension(path)     # ✅

# Directory operations - WORKS TODAY
files = list_dir("/path")   # returns Result<List<text>, text> ✅
matches = glob("*.txt")     # ✅
found = find_files("/dir", "*.rs")  # ✅

# Low-level file descriptor operations
fd = open_file("data.txt", "r")?  # ✅
close_file(fd)                     # ✅
```

---

## 5. Identified Inconsistencies & Gaps

### 5.1 Naming Consistency Strategy (Actual vs Recommended)

| Concept | Doc Suggested | Actual in Code | Status | Opinion |
|---------|--------------|----------------|--------|---------|
| Length | `len` | `len` | ✅ Same | Good |
| Add to end | `push` | `push`, `append` | ✅ Same | Both work |
| Whitespace trim | `trim` | `trim`, `strip` | ✅ Same | Both work |
| Uppercase | `up` | `upper` | ⚠️ Longer | Consider adding `up` alias |
| Lowercase | `down` | `lower` | ⚠️ Longer | Consider adding `down` alias |
| Reverse | `rev` | `reverse` | ⚠️ Longer | Consider adding `rev` alias |
| Substring check | `contains` | `contains` | ✅ Same | Good |
| Empty check | `empty` | `is_empty` | ⚠️ Longer | Consider adding `empty` alias |

### 5.2 Predicate Naming (Two Patterns)

**Updated convention**: Simple now uses two patterns for predicates:

1. **Existence checks → Use `.?` operator**
2. **Value predicates → Keep `is_` prefix**

```simple
# EXISTENCE CHECKS - Use .? operator
opt.?             # replaces is_some()
not opt.?         # replaces is_none()
list.?            # replaces not is_empty() - true if has items
not list.?        # replaces is_empty() - true if empty
result.ok.?       # replaces is_ok()
result.err.?      # replaces is_err()

# VALUE PREDICATES - Keep is_ prefix (these check properties, not existence)
n.is_even         # checks if value is even (n exists, checking property)
n.is_odd          # checks if value is odd
n.is_positive     # checks if n > 0
n.is_negative     # checks if n < 0
n.is_zero         # checks if n == 0
f.is_nan          # checks if float is NaN
f.is_infinite     # checks if float is infinite
Path.is_file(p)   # checks if path is a file
Path.is_dir(p)    # checks if path is a directory
```

**Key distinction**:
- `.?` = "Does this value exist/have content?" (existence/presence)
- `is_*` = "What property does this value have?" (value predicate)

| Pattern | Use `.?` | Use `is_` | Reason |
|---------|----------|-----------|--------|
| `is_some`/`is_none` | ✅ `opt.?` | ❌ | Existence check |
| `is_ok`/`is_err` | ✅ `result.ok.?` | ❌ | Existence check |
| `is_empty` (collections) | ✅ `not list.?` | ❌ | Existence check |
| `is_even`/`is_odd` | ❌ | ✅ `n.is_even` | Value property |
| `is_positive`/`is_negative` | ❌ | ✅ `n.is_positive` | Value property |
| `is_nan`/`is_infinite` | ❌ | ✅ `f.is_nan` | Value property |
| `is_file`/`is_dir` | ❌ | ✅ `Path.is_file(p)` | Value property |

### 5.3 Mutability Story

Since Simple uses **immutability by default**, the API can be simpler:
- Drop Ruby's `!` mutation suffix entirely
- All methods return new values
- Use `->` operator for reassignment sugar

```simple
# No need for sort vs sort! distinction
lst = lst.sort              # explicit reassignment
lst->sort                   # sugar for above

# Chainable transformations return new values
result = data.filter(\x: x > 0).sort.take(10)
```

### 5.4 Missing Builder Pattern

Spec mentions `StringBuilder` but doesn't detail it (stdlib needed):

```simple
# Needed for efficient string building (stdlib)
let sb = StringBuilder()
sb.append("Hello")
sb.append(" ")
sb.append("World")
s = sb.to_string        # => "Hello World"

# Or functional style (needs join in stdlib)
s = ["Hello", " ", "World"].join("")
```

### 5.5 Safe Navigation ✅ IMPLEMENTED

Safe navigation is fully implemented:

```simple
# Safe navigation operator - IMPLEMENTED
user.address.city            # crashes if address is nil
user?.address?.city          # returns nil if any is nil
user?.address?.city ?? "Unknown"  # with default via ??

# Method chaining with optional
result?.process()?.validate()
```

### 5.6 Range Object Details ✅ IMPLEMENTED (Grammar)

Range syntax is implemented. Range methods need stdlib:

```simple
# Range literals - IMPLEMENTED
1..10       # exclusive range (1 to 9)
1..=10      # inclusive range (1 to 10)

# Range methods (need stdlib implementation)
(1..10).contains(5)     # => true
(1..10).to_vec          # => [1,2,3,4,5,6,7,8,9]
(1..10).step(2)         # => [1,3,5,7,9]
(1..10).len             # => 9
```

---

## 6. Gap-Finding Checklist

### Audit Procedure for `public_api.yml`

1. **Extract** exported method list per type: `String`, `Int`, `Float`, `Vec`, `Dict`, `Set`, `File`, `Path`
2. **Normalize** names (snake_case) to avoid cosmetic differences
3. **Diff** against baseline clusters (above tables)
4. **Flag**:
   - **Missing**: No equivalent exists
   - **Inconsistent**: Same concept has multiple names
   - **Non-orthogonal**: Method exists only on one collection type
   - **Verbosity leaks**: Common tasks require 3+ calls/imports

### Consistency Checks

| Check | Pass Criteria |
|-------|---------------|
| **Unified iteration** | `map/filter/reduce/any/all/find/zip/enumerate` on ALL collections |
| **Consistent naming** | Same concept = same name across types |
| **Chainable returns** | Non-mutating methods return `self` type |
| **One-liner file ops** | `File.read/write/lines` exist |
| **Existence checks** | Use `.?` operator (not `is_some`, `is_empty`) |
| **Value predicates** | Use `is_` prefix (`is_even`, `is_positive`, `is_nan`) |

---

## 7. Ruby-Style Simplicity Scorecard

| Aspect | Ruby | Python | Simple (Current) | Simple (Target) |
|--------|------|--------|------------------|-----------------|
| Method name length | ⭐⭐⭐⭐⭐ Short | ⭐⭐⭐ Medium | ⭐⭐⭐ Medium | ⭐⭐⭐⭐ Short |
| Predicate naming | `?` suffix | `is_` prefix | ❓ Not specified | No suffix |
| Chainable methods | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ (`->`) | ⭐⭐⭐⭐⭐ |
| Block syntax | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐⭐ (`\x:`) | ⭐⭐⭐⭐⭐ |
| One-liner file I/O | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ❌ Missing | ⭐⭐⭐⭐⭐ |
| Optional parens | ⭐⭐⭐⭐⭐ | ❌ | ⭐⭐⭐⭐ (stmt) | ⭐⭐⭐⭐ |
| Unified iteration | ⭐⭐⭐⭐⭐ Enumerable | ⭐⭐⭐ | ⚠️ Iterable partial | ⭐⭐⭐⭐⭐ |

---

## 8. Implementation Classification: API vs Grammar/Compiler

### 8.1 Grammar/Parser Feature Status

**Last verified**: 2026-01-24 against parser source code.

#### Already Implemented (Grammar)

| Feature | Syntax | Evidence |
|---------|--------|----------|
| **Safe navigation `?.`** | `user?.address?.city` | `token.rs:336` - `QuestionDot`, `postfix.rs:329` |
| **Range literals** | `1..10` (exclusive), `1..=10` (inclusive) | `token.rs:331-333`, `core.rs:565-569` |
| **String interpolation** | `"Hello, {name}!"` | `token.rs:102` - `FString`, `lexer/strings.rs` |
| **Raw strings** | `r"no\escape"` or `'single quotes'` | `lexer/strings.rs:5-49` |
| **Slice syntax** | `lst[1:5]`, `lst[::2]`, `lst[1:5:2]` | `postfix.rs:78-148`, `core.rs:524-530` |
| **Negative indexing** | `lst[-1]`, `lst[-2]` | Works via unary minus expression |
| **Spread operator** | `[...a, ...b]`, `{**d1, **d2}` | `token.rs:333`, `core.rs:531-534` |
| **Named arguments** | `foo(x: 1, y: 2)` or `foo(x=1, y=2)` | `helpers.rs:202-289` |
| **Default parameters** | `fn foo(x: Int = 0)` | `core.rs:270-280` |
| **Variadic parameters** | `fn foo(args...)` | `core.rs:279` |
| **Destructuring** | `let (a, b) = tuple`, `let [x, y] = arr` | `core.rs:802-807` |
| **Pattern guards** | `match x: case n if n > 0:` | `core.rs:898-903` |
| **List comprehension** | `[x*2 for x in lst if x > 0]` | `core.rs:509-515` |
| **Dict comprehension** | `{k: v for k, v in items}` | `core.rs:516-523` |
| **With statement** | `with File.open(p) as f:` | `token.rs:193`, `statements.rs:248-253` |
| **Chained comparison** | `0 < x < 10` → `(0 < x) and (x < 10)` | `binary.rs:77-134` |
| **Null coalescing** | `x ?? default` | `token.rs:335`, `core.rs:625-630` |

#### Partially Implemented (Grammar)

| Feature | Status | Notes |
|---------|--------|-------|
| **Range step** | ⚠️ Partial | Slice `[a:b:step]` works, but `1..10 by 2` keyword not implemented |
| **Regex literals** | ⚠️ Partial | Use `"pattern"_re` literal function, not `/pattern/` native syntax |
| **Multiple assignment** | ⚠️ Partial | Use `let (a, b) = (b, a)` via destructuring |

#### Not Implemented (Grammar)

| Feature | Description | Complexity | Notes |
|---------|-------------|------------|-------|
| **Byte strings** | `b"bytes"` | Low | No token type in lexer |
| **For-else** | `for x in lst: ... else: ...` | Low | `ForStmt` lacks else clause |
| **Elvis operator** | `x ?: default` | Low | Use `??` instead |
| **Pipeline operator** | `x \|> f \|> g` | Low | Use method chaining or `->` |

#### Implemented (Grammar) - Ruby-like Brevity

| Feature | Description | Complexity | Notes |
|---------|-------------|------------|-------|
| **Existence `.?`** | `expr.?` returns bool | ✅ Implemented | Postfix operator, check non-nil AND non-empty |
| **No-paren methods** | `list.first` for no-arg methods | ✅ Implemented | Falls back to method call if property not found |

**Existence Operator `.?` Implementation:**

```
# Grammar addition
postfix_expr: expr '.' '?'  →  Expr::Exists(expr)

# Semantics: returns true if value is "present"
# - Option<T>: true if Some
# - List/Set/Dict: true if non-empty
# - String: true if non-empty
# - Numbers/Bool: always true (they are values)
```

**No-Paren Methods Implementation:**

```
# Grammar change
field_access: expr '.' identifier
  → if identifier is no-arg method: MethodCall(expr, identifier, [])
  → else: FieldAccess(expr, identifier)

# Examples
list.empty      →  list.empty()      # method call
list.len        →  list.len()        # method call
obj.field       →  obj.field         # field access (not a method)
```

**Combined Example:**

```simple
# With both features
if user?.profile?.tags.?:       # safe nav + existence check
    for tag in user!.profile!.tags:
        print tag.upper.trim    # no-paren method chain
```

### 8.2 Requires Type System/Compiler Changes

These need changes to type checking, inference, or code generation:

| Feature | Description | Complexity | Notes |
|---------|-------------|------------|-------|
| **Trait/Interface methods** | Add methods to `Iterable` trait | Medium | Trait definition + impls |
| **Extension methods** | Add methods to existing types | Medium | If not already supported |
| **Generic constraints** | `fn sort<T: Comparable>` | Medium | Bound checking |
| **Associated types** | `trait Iter { type Item }` | High | Type-level programming |
| **Union types** | `Int \| String` | High | Type system expansion |
| **Optional type `T?`** | Sugar for `Option<T>` | Low | Type alias + inference |
| **Result type** | `Result<T, E>` with `?` operator | Medium | Error propagation |
| **Const generics** | `Array<T, N>` fixed-size | High | Compile-time values |
| **Method overloading** | Multiple signatures | Medium | Resolution rules |
| **Operator overloading** | Custom `+`, `-`, etc. | Medium | Trait-based dispatch |
| **Implicit conversions** | `Int` to `Float` auto | Low | Coercion rules |
| **Type inference for closures** | Infer `\x: x + 1` types | Medium | Bidirectional inference |
| **Higher-kinded types** | `Functor<F<_>>` | Very High | Advanced type system |

### 8.3 Requires Runtime/Interpreter Changes

These need changes to the runtime, GC, or interpreter:

| Feature | Description | Complexity | Notes |
|---------|-------------|------------|-------|
| **Iterator protocol** | Lazy iteration support | Medium | `next()` method + state |
| **Generator/yield** | `yield` keyword | High | Coroutine/continuation |
| **Context managers** | `__enter__`/`__exit__` protocol | Medium | Resource cleanup |
| **Finalizers** | Destructor callbacks | Medium | GC integration |
| **Weak references** | Non-preventing GC refs | Medium | GC support |
| **Exception chaining** | `raise X from Y` | Low | Exception metadata |
| **Stack traces** | Source location in errors | Medium | Debug info preservation |
| **Reflection** | Runtime type info | High | Type metadata storage |
| **Dynamic dispatch** | Trait objects / vtables | Medium | If not already present |

### 8.4 API/Stdlib Only (No Grammar/Compiler Changes)

These can be implemented purely as library functions/methods:

#### String Methods
| Method | Implementation Notes |
|--------|---------------------|
| `len` | Field access or native call |
| `empty` | `self.len == 0` |
| `trim`, `ltrim`, `rtrim` | Character iteration |
| `up`, `down`, `capitalize` | Unicode mapping |
| `rev` | Reverse iteration |
| `split(sep)` | Find + slice loop |
| `join(iter)` | StringBuilder pattern |
| `replace(old, new)` | Find + rebuild |
| `find`, `rfind` | Linear scan |
| `contains` | `find(...) != -1` |
| `starts_with`, `ends_with` | Prefix/suffix compare |
| `count` | Count occurrences |
| `repeat(n)` | Loop append |
| `chars`, `bytes`, `lines` | Iterator wrappers |
| `to_int`, `to_float` | Parsing logic |
| `pad_left`, `pad_right`, `center` | String building |
| `is_digit`, `is_alpha`, `is_space` | Character class checks |

#### Number Methods
| Method | Implementation Notes |
|--------|---------------------|
| `abs` | Conditional negate |
| `floor`, `ceil`, `round`, `trunc` | Math intrinsics |
| `clamp(min, max)` | `max(min, min(self, max))` |
| `sign` | Conditional return -1/0/1 |
| `even`, `odd` | `self % 2 == 0` |
| `positive`, `negative`, `zero` | Comparison |
| `between(a, b)` | `a <= self <= b` |
| `divmod` | `(self / n, self % n)` |
| `to_string`, `to_int`, `to_float` | Conversion |
| `is_nan`, `is_inf` | Float bit checks |
| `bit_len`, `popcount` | Bit operations |

#### Collection Methods (on Vec/List)
| Method | Implementation Notes |
|--------|---------------------|
| `len`, `empty` | Field/property |
| `first`, `last` | Index access with bounds |
| `push`, `pop` | Buffer manipulation |
| `insert`, `remove_at` | Shift elements |
| `clear` | Reset length |
| `take(n)`, `drop(n)` | Slice/view |
| `slice(a, b)` | Subarray view/copy |
| `concat` | Append loop |
| `rev` | Reverse iteration |
| `sort`, `sort_by` | Quicksort/mergesort impl |
| `uniq` | Set-based dedup |
| `flat` | Recursive append |
| `compact` | Filter non-nil |
| `contains` | Linear scan |
| `index` | Linear scan with index |
| `count` | Filter + len |
| `min`, `max`, `sum` | Reduce operations |
| `join(sep)` | StringBuilder |
| `shuffle`, `sample` | Random + swap |

#### Iterable Trait Methods (if trait system supports it)
| Method | Implementation Notes |
|--------|---------------------|
| `map` | Iterator transform |
| `filter` | Iterator predicate |
| `reduce`, `fold` | Accumulator loop |
| `any`, `all`, `none` | Short-circuit scan |
| `find`, `find_index` | Short-circuit scan |
| `zip` | Parallel iteration |
| `enumerate` | Index + value pairs |
| `group_by` | Dict accumulation |
| `partition` | Two-list accumulation |
| `take_while`, `drop_while` | Predicate iteration |
| `flat_map` | Map + flatten |
| `chunk`, `each_slice`, `each_cons` | Windowed iteration |

#### Dict Methods
| Method | Implementation Notes |
|--------|---------------------|
| `len`, `empty` | Property |
| `get(key, default)` | Lookup with fallback |
| `set`, `remove` | Hash table ops |
| `contains_key`, `contains_value` | Lookup/scan |
| `keys`, `values`, `items` | Iterator views |
| `merge` | Insert loop |
| `invert` | Rebuild swapped |
| `select`, `reject` | Filter iteration |
| `transform_keys`, `transform_values` | Map rebuild |

#### Set Methods
| Method | Implementation Notes |
|--------|---------------------|
| `len`, `empty` | Property |
| `add`, `remove`, `contains` | Hash set ops |
| `union`, `intersect`, `diff` | Set algebra |
| `symmetric_diff` | XOR operation |
| `subset`, `superset` | Containment check |

#### File/Path Methods
| Method | Implementation Notes |
|--------|---------------------|
| `File.read`, `File.write` | OS calls |
| `File.lines` | Read + split |
| `File.exists`, `is_file`, `is_dir` | Stat calls |
| `File.size`, `File.delete`, `File.rename` | OS calls |
| `File.copy`, `File.move` | Read/write or OS |
| `Path.join` | String concat with sep |
| `Path.dirname`, `Path.basename`, `Path.ext` | String parsing |
| `Path.normalize`, `Path.absolute` | OS path resolution |
| `Dir.list`, `Dir.glob` | OS directory calls |
| `Dir.mkdir`, `Dir.rmdir` | OS calls |

---

## 9. Priority Implementation Backlog

### Tier 1: API-Only (No Compiler Changes)

**String essentials** (stdlib only):
```simple
trim, ltrim, rtrim       # whitespace removal
up, down, capitalize     # case conversion
split, join              # split/join operations
replace                  # substring replacement
find, rfind              # search
contains, starts_with, ends_with  # predicates
len, empty               # basic properties
to_int, to_float         # parsing
rev                      # reverse
```

**Number essentials** (stdlib only):
```simple
abs, floor, ceil, round, trunc   # math
clamp, sign                      # range/sign
even, odd, positive, negative, zero  # predicates
divmod                           # division
to_string                        # conversion
```

**Collection essentials** (stdlib only):
```simple
# Vec
len, empty, first, last
push, pop, clear
take, drop, slice
sort, sort_by, rev, uniq
contains, index, count
min, max, sum
join

# Dict
len, empty
get(key, default), set, remove
keys, values, items
contains_key, merge

# Set
add, remove, contains
union, intersect, diff
```

**File one-liners** (stdlib only):
```simple
File.read(path)
File.write(path, content)
File.lines(path)
File.exists(path)
Path.join(parts...)
Path.dirname, Path.basename, Path.ext
Dir.list(path)
```

**Iterable trait methods** (stdlib, needs trait impl):
```simple
# Full Iterable trait definition
trait Iterable<T>:
    fn map<U>(f: Fn(T) -> U) -> Self<U>
    fn filter(f: Fn(T) -> Bool) -> Self<T>
    fn reduce<U>(init: U, f: Fn(U, T) -> U) -> U
    fn any(f: Fn(T) -> Bool) -> Bool
    fn all(f: Fn(T) -> Bool) -> Bool
    fn none(f: Fn(T) -> Bool) -> Bool
    fn find(f: Fn(T) -> Bool) -> Option<T>
    fn find_index(f: Fn(T) -> Bool) -> Option<Int>
    fn zip<U>(other: Iterable<U>) -> Iterable<(T, U)>
    fn enumerate() -> Iterable<(Int, T)>
    fn group_by<K>(f: Fn(T) -> K) -> Dict<K, Vec<T>>
    fn partition(f: Fn(T) -> Bool) -> (Self<T>, Self<T>)
    fn take(n: Int) -> Self<T>
    fn drop(n: Int) -> Self<T>
    fn take_while(f: Fn(T) -> Bool) -> Self<T>
    fn drop_while(f: Fn(T) -> Bool) -> Self<T>
    fn flat_map<U>(f: Fn(T) -> Iterable<U>) -> Self<U>
```

### Tier 2: Remaining Grammar/Parser Changes

Most grammar features are already implemented. Remaining items:

| Feature | Priority | Effort | Benefit |
|---------|----------|--------|---------|
| **Byte strings `b"..."`** | Low | Low | Binary data handling |
| **For-else** | Low | Low | Python-style loop completion |
| **Range step `by` keyword** | Low | Medium | `1..10 by 2` syntax sugar |
| **Native regex `/re/`** | Low | Medium | Alternative to `"re"_re` |

**Already Implemented (use these!):**
```simple
# Slice syntax - IMPLEMENTED
lst[1:5]        # slice from index 1 to 5
lst[:-1]        # all but last
lst[::2]        # every other element
lst[1:10:2]     # slice with step

# Negative indexing - IMPLEMENTED
lst[-1]         # last element
lst[-2]         # second to last

# Safe navigation - IMPLEMENTED
user?.address?.city     # nil if any nil
d.get("key")?.process() # chain with optional

# Null coalescing - IMPLEMENTED
name ?? "Unknown"       # default if nil
config["port"] ?? 8080

# With statement - IMPLEMENTED
with File.open("data.txt") as f:
    content = f.read
# auto-close after block

# Comprehensions - IMPLEMENTED
[x * 2 for x in lst if x > 0]        # list comprehension
{k: v for k, v in items if v > 0}    # dict comprehension

# Destructuring - IMPLEMENTED
let (a, b) = get_pair()
let [first, second, ...rest] = arr

# Chained comparison - IMPLEMENTED
if 0 < x < 10:    # desugars to (0 < x) and (x < 10)
    print "in range"
```

### Tier 3: Requires Type System/Compiler Changes

| Feature | Priority | Effort | Benefit |
|---------|----------|--------|---------|
| **Extension methods** | High | Medium | Add methods to existing types |
| **Optional type `T?`** | High | Low | Sugar for `Option<T>` |
| **Generic constraints** | Medium | Medium | `sort` needs `Comparable` |
| **Operator overloading** | Medium | Medium | Custom types feel native |
| **Result + `?` operator** | Medium | Medium | Error propagation |
| **Union types** | Low | High | Flexibility |

**Recommended Type System Additions:**
```simple
# Optional type sugar (HIGH PRIORITY)
fn find(key: String) -> Int?    # same as Option<Int>

# Extension methods (HIGH PRIORITY)
extend String:
    fn word_count(self) -> Int:
        self.split(" ").len

# Generic constraints (MEDIUM PRIORITY)
fn sort<T: Comparable>(lst: Vec<T>) -> Vec<T>

fn max<T: Comparable>(a: T, b: T) -> T:
    if a > b: a else: b
```

### Tier 4: Requires Runtime Changes

| Feature | Priority | Effort | Benefit |
|---------|----------|--------|---------|
| **Iterator protocol** | High | Medium | Lazy evaluation |
| **Context managers** | Medium | Medium | Resource cleanup |
| **Generator/yield** | Low | High | Lazy sequences |
| **Reflection** | Low | High | Metaprogramming |

---

## 10. Summary: What to Implement Where

### Immediate (API/Stdlib Only)
- All string methods: `trim`, `split`, `join`, `replace`, `contains`, etc.
- All number methods: `abs`, `round`, `clamp`, `even`, `odd`, etc.
- Collection methods: `first`, `last`, `sum`, `min`, `max`, `sort`, etc.
- File convenience: `File.read`, `File.write`, `File.lines`, `File.exists`
- Path utilities: `Path.join`, `Path.dirname`, `Path.basename`

**Estimated effort**: Medium (pure library work, no compiler changes)

### Short-term (Grammar Changes)
- Slice syntax `[a:b]` - very high value for Ruby/Python feel
- Negative indexing `[-1]` - expected by Ruby/Python users
- Safe navigation `?.` - modern nil handling

**Estimated effort**: Low-Medium per feature

### Medium-term (Type System)
- Optional type sugar `T?`
- Extension methods
- Generic constraints for `Comparable`, `Hashable`

**Estimated effort**: Medium per feature

### Long-term (Runtime)
- Lazy iterator protocol
- Context manager protocol
- Generator support

**Estimated effort**: High per feature

---

## 11. Quick Reference: Implementation Location

| Want to add... | Change needed in... | Status |
|----------------|---------------------|--------|
| `String.trim` | stdlib only | Needs stdlib |
| `Vec.sort` | stdlib only | Needs stdlib |
| `File.read` | stdlib + OS bindings | Needs stdlib |
| `lst[1:5]` slice | ~~parser + AST~~ | ✅ **Implemented** |
| `lst[-1]` negative index | ~~parser or runtime~~ | ✅ **Implemented** |
| `user?.name` safe nav | ~~parser + type checker~~ | ✅ **Implemented** |
| `x ?? default` | ~~parser~~ | ✅ **Implemented** |
| **`expr.?` existence** | parser + runtime | ✅ **Implemented** |
| **`list.first` no-paren** | interpreter | ✅ **Implemented** |
| `fn f() -> Int?` | **type system** | Needs type system |
| `extend String` | **type system** | Needs type system |
| `yield x` generators | **parser + runtime** | Needs parser + runtime |
| `with file as f:` | ~~parser + runtime protocol~~ | ✅ **Implemented** (parser done)

---

## 12. Final Summary

**Last updated**: 2026-01-24 (After `.?` and no-paren implementation)

### Implementation Breakdown (Revised)

| Category | Count | Status |
|----------|-------|--------|
| **API/Stdlib** | ~170+ methods | ✅ **~80% Implemented** |
| **Grammar/Parser** | ~20 features | ✅ **19 implemented**, 2 remaining |
| **Ruby-like brevity** | 2 features | ✅ **DONE** (`.?` + no-paren) |
| **Type System** | ~6 features | Needs implementation |
| **Runtime** | ~4 features | Partial |

### Stdlib Coverage Summary

| Type | Suggested | Implemented | Coverage |
|------|-----------|-------------|----------|
| **String** | 28 methods | 28+ methods | ✅ 100% |
| **Int** | 15 methods | 25+ methods | ✅ 100%+ |
| **Float** | 15 methods | 30+ methods | ✅ 100%+ |
| **Array/Vec** | 28 methods | 40+ methods | ✅ 100%+ |
| **Dict/Map** | 16 methods | 18+ methods | ✅ 90% |
| **Set** | 11 methods | 15+ methods | ✅ 100%+ |
| **File I/O** | 22 methods | 15 methods | ⚠️ 70% |
| **Path** | 9 methods | 7 methods | ⚠️ 80% |
| **Directory** | 10 methods | 6 methods | ⚠️ 60% |

### Key Finding: Two Predicate Patterns

Simple now uses **two distinct patterns** for predicates:

| Type | Pattern | Example | Rationale |
|------|---------|---------|-----------|
| **Existence checks** | `.?` operator | `opt.?`, `list.?`, `result.ok.?` | Checks presence/content |
| **Value predicates** | `is_` prefix | `n.is_even`, `n.is_positive`, `f.is_nan` | Checks value property |

This is cleaner than Ruby's uniform `?` suffix because it distinguishes:
- "Does this exist?" → `.?`
- "What property does this have?" → `is_*`

### What Makes Ruby Feel "Short" - Status

1. **Unified iteration** - ✅ **IMPLEMENTED**: `map`, `filter`, `reduce`, `any`, `all`, `find`, `zip`, `enumerate`, `group_by`
2. **One-liner file ops** - ✅ **IMPLEMENTED**: `read_file()`, `write_file()` (longer names than Ruby)
3. **Chainable everything** - ✅ **IMPLEMENTED**: All methods return values
4. **Existence check `.?`** - ✅ **IMPLEMENTED**: `opt.?`, `list.?`, `result.ok.?` (replaces Ruby's `nil?`, `present?`, `empty?`, `ok?`)
5. **No-paren methods** - ✅ **IMPLEMENTED**: `list.first`, `s.upper`, `s.trim` (like Ruby's property-style access)
6. **Slice syntax** - ✅ **IMPLEMENTED**: `[1:5]`, `[-1]`
7. **Safe nil handling** - ✅ **IMPLEMENTED**: `?.` and `??` operators
8. **Value predicates** - ✅ **DECIDED**: Keep `is_` prefix for value predicates (`is_even`, `is_positive`) - these check properties, not existence

### Remaining Gaps

**File I/O:**
- ❌ `File.lines(path)` - read as line array
- ❌ `File.append(path, content)` - append mode
- ❌ Binary file operations
- ❌ `Dir.walk()` - recursive directory traversal
- ❌ `Dir.mkdir_p()` - create with parents
- ❌ `Dir.cwd()`, `Dir.chdir()` - working directory

**Dict:**
- ❌ `contains_value`
- ❌ `invert`
- ❌ `transform_keys`

**Numbers:**
- ❌ `divmod`
- ❌ `between`

### Implemented: Ruby-like Brevity Strategy

**Both grammar features are now implemented:**

1. ✅ **`.?` existence operator** (grammar change) - DONE
2. ✅ **No-paren method calls** (grammar change) - DONE

#### Implemented Grammar Features:

```simple
# Existence check with .? - IMPLEMENTED
if user.?:                  # Ruby: !user.nil?
if list.?:                  # Ruby: !list.empty?
if dict["key"].?:           # Ruby: hash.key?("key")
if result.ok.?:             # Ruby: result.ok?
if result.err.?:            # Ruby: result.err?

# No-paren methods - IMPLEMENTED
list.first                  # Ruby: list.first (no parens)
list.last                   # Ruby: list.last
s.trim                      # Ruby: s.strip
s.upper                     # Ruby: s.upcase
s.lower                     # Ruby: s.downcase

# Combined with chaining - IMPLEMENTED
user?.profile?.tags.?       # exists and non-empty
text.trim.lower.split(",")  # no parens for no-arg methods
list.first.?                # first element exists
```

### Naming Convention (Current)

```simple
# Existence checks - Use .?
opt.?                       # is Some (replaces is_some())
not opt.?                   # is None (replaces is_none())
list.?                      # is non-empty (replaces not is_empty())
not list.?                  # is empty (replaces is_empty())
result.ok.?                 # is Ok (replaces is_ok())
result.err.?                # is Err (replaces is_err())

# Value predicates - Keep is_
n.is_even                   # value property (no-paren call)
n.is_odd                    # value property
n.is_positive               # value property
n.is_negative               # value property
n.is_zero                   # value property
f.is_nan                    # value property
f.is_infinite               # value property
```

### Implementation Status

| Feature | Type | Status | Impact |
|---------|------|--------|--------|
| `.?` existence | Grammar | ✅ DONE | Replaces ~15 Ruby patterns |
| No-paren methods | Grammar | ✅ DONE | All no-arg methods |
| Keep `is_` for value predicates | Convention | ✅ DECIDED | Clarity for value checks |