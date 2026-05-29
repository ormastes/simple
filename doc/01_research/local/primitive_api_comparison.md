# Primitive and Collection API Comparison: Simple vs Ruby vs Python

**Date:** 2026-01-19
**Purpose:** Identify missing methods to add for API completeness and consistency

## Sources

### Ruby Documentation
- [Ruby String API v3.4](https://rubyapi.org/3.4/o/string)
- [Ruby Integer API (Master)](https://docs.ruby-lang.org/en/master/Integer.html)
- [Ruby Array API v3.4](https://rubyapi.org/3.4/o/array)
- [Ruby Hash Reference](https://ruby-doc.org/core-2.7.0/Hash.html)
- [Ruby Numeric API](https://docs.ruby-lang.org/en/3.2/Numeric.html)

### Python Documentation
- [Python String Methods (v3.14.2)](https://docs.python.org/3/library/stdtypes.html)
- [Python Data Structures (v3.14.2)](https://docs.python.org/3/tutorial/datastructures.html)
- [Python Set Objects](https://docs.python.org/3/c-api/set.html)
- [Python Dictionary Methods](https://www.w3schools.com/python/python_ref_dictionary.asp)

---

## String Methods Comparison

### ✅ Already Implemented in Simple (30+ methods)

**Basic:** `len()`, `char_count()`, `is_empty()`, `chars()`, `bytes()`
**Search:** `contains()`, `starts_with()`, `ends_with()`, `find()`, `rfind()`, `index_of()`, `last_index_of()`, `count()`
**Case:** `to_upper()`, `to_lower()`
**Trim:** `trim()`, `strip()`, `trim_start()`, `trim_end()`
**Manipulation:** `substring()`, `slice()`, `char_at()`, `replace()`, `replace_first()`, `split()`, `split_lines()`, `repeat()`, `reverse()`, `sorted()`
**Padding:** `pad_left()`, `pad_right()`
**Checking:** `is_numeric()`, `is_alpha()`, `is_alphanumeric()`, `is_whitespace()`
**Parsing:** `parse_int()`, `parse_float()`, `to_int()`, `to_float()`
**Manipulation:** `take()`, `drop()`, `append()`, `prepend()`, `push()`, `pop()`, `clear()`

### ❌ Missing String Methods

| Method | Ruby | Python | Description | Priority |
|--------|------|--------|-------------|----------|
| `capitalize()` | ✅ | ✅ | Uppercase first char, lowercase rest | HIGH |
| `swapcase()` | ✅ | ✅ | Swap case of all characters | MEDIUM |
| `title()` / `titlecase()` | ✅ | ✅ | Titlecase each word | MEDIUM |
| `center(width, fillchar)` | ❌ | ✅ | Center string with padding | MEDIUM |
| `ljust(width, fillchar)` | ❌ | ✅ | Left-justify (alias for pad_right) | LOW (alias) |
| `rjust(width, fillchar)` | ❌ | ✅ | Right-justify (alias for pad_left) | LOW (alias) |
| `zfill(width)` | ❌ | ✅ | Pad with zeros on left | MEDIUM |
| `removeprefix(prefix)` | ✅ | ✅ | Remove prefix if present | HIGH |
| `removesuffix(suffix)` | ✅ | ✅ | Remove suffix if present | HIGH |
| `partition(sep)` | ✅ | ✅ | Split into [before, sep, after] | MEDIUM |
| `rpartition(sep)` | ✅ | ✅ | Split from right into [before, sep, after] | MEDIUM |
| `chomp()` | ✅ | ❌ | Remove trailing newline/record separator | MEDIUM |
| `chop()` | ✅ | ❌ | Remove last character | LOW |
| `squeeze(chars)` | ✅ | ❌ | Remove duplicate adjacent chars | MEDIUM |
| `casefold()` | ❌ | ✅ | Aggressive lowercase for comparison | LOW |
| `expandtabs(tabsize)` | ❌ | ✅ | Replace tabs with spaces | LOW |
| `isidentifier()` | ❌ | ✅ | Check if valid identifier | LOW |
| `istitle()` | ❌ | ✅ | Check if titlecased | LOW |
| `isdecimal()` | ❌ | ✅ | Check if all decimal digits | LOW |
| `translate(table)` | ✅ | ✅ | Character translation | LOW |

---

## Integer/Number Methods Comparison

### ✅ Already Implemented in Simple (40+ methods)

**Arithmetic:** `abs()`, `sign()`, `pow()`, `min()`, `max()`, `clamp()`
**Predicates:** `is_zero()`, `is_positive()`, `is_negative()`, `is_even()`, `is_odd()`, `is_power_of_two()`
**Bit Operations:** `bit_count()`, `count_ones()`, `leading_zeros()`, `trailing_zeros()`, `to_hex()`, `to_bin()`, `to_oct()`
**Euclidean:** `div_euclid()`, `rem_euclid()`
**Overflow:** `checked_add/sub/mul()`, `saturating_add/sub/mul()`, `wrapping_add/sub/mul()`
**Power:** `next_power_of_two()`
**Iteration:** `times()`, `upto()`, `downto()`, `up_to()`, `down_to()`
**Conversion:** `to_float()`, `to_string()`

### ❌ Missing Integer Methods

| Method | Ruby | Python | Description | Priority |
|--------|------|--------|-------------|----------|
| `gcd(other)` | ✅ | ❌ | Greatest common divisor | HIGH |
| `lcm(other)` | ✅ | ❌ | Least common multiple | HIGH |
| `digits(base)` | ✅ | ❌ | Array of digits (least significant first) | MEDIUM |
| `bit_length()` | ❌ | ✅ | Number of bits needed to represent | MEDIUM |
| `chr()` | ✅ | ✅ | Convert to Unicode character | MEDIUM |
| `ord()` | ✅ | ✅ | Get Unicode code point (for String) | N/A |
| `numerator` | ✅ | ❌ | Numerator (returns self for integers) | LOW |
| `denominator` | ✅ | ❌ | Denominator (returns 1 for integers) | LOW |
| `allbits?(mask)` | ✅ | ❌ | Check if all bits in mask are set | LOW |
| `anybits?(mask)` | ✅ | ❌ | Check if any bits in mask are set | LOW |
| `nobits?(mask)` | ✅ | ❌ | Check if no bits in mask are set | LOW |
| `succ()` / `next()` | ✅ | ❌ | Return next integer (n+1) | LOW |
| `pred()` | ✅ | ❌ | Return previous integer (n-1) | LOW |
| `as_integer_ratio()` | ❌ | ✅ | For floats: return (numerator, denominator) | MEDIUM |

---

## Float Methods Comparison

### ✅ Already Implemented in Simple (35+ methods)

**Rounding:** `floor()`, `ceil()`, `round()`, `trunc()`, `fract()`, `round_to()`
**Absolute:** `abs()`, `sign()`, `min()`, `max()`, `clamp()`
**Predicates:** `is_zero()`, `is_positive()`, `is_negative()`, `is_nan()`, `is_infinite()`, `is_finite()`
**Power/Log:** `sqrt()`, `cbrt()`, `pow()`, `exp()`, `exp2()`, `ln()`, `log()`, `log2()`, `log10()`
**Trig:** `sin()`, `cos()`, `tan()`, `asin()`, `acos()`, `atan()`, `atan2()`, `sinh()`, `cosh()`, `tanh()`
**Angle:** `to_degrees()`, `to_radians()`
**Special:** `hypot()`, `recip()`, `mul_add()`
**Conversion:** `to_int()`, `to_string()`

### ❌ Missing Float Methods

| Method | Ruby | Python | Description | Priority |
|--------|------|--------|-------------|----------|
| `as_integer_ratio()` | ❌ | ✅ | Return (numerator, denominator) tuple | MEDIUM |
| `hex()` | ❌ | ✅ | Hexadecimal representation | LOW |
| `fromhex(string)` | ❌ | ✅ | Parse hex string to float | LOW |
| `is_integer()` | ❌ | ✅ | Check if no fractional part | MEDIUM |

---

## Collection Methods Comparison

### Array/List Methods

#### ✅ Already Implemented in Simple (50+ methods)

**Core:** `len()`, `is_empty()`, `first()`, `last()`, `get()`, `[index]`
**Functional:** `map()`, `filter()`, `reduce()`, `flat_map()`, `flatten()`
**Mutation:** `push()`, `pop()`, `insert()`, `remove()`, `reverse()`, `slice()`, `concat()`
**Selection:** `take()`, `skip()`, `take_while()`, `skip_while()`, `enumerate()`, `zip()`
**Grouping:** `chunk()`, `partition()`, `group_by()`, `unique()`
**Aggregation:** `contains()`, `find()`, `index_of()`, `sum()`, `min()`, `max()`, `count()`, `join()`, `any()`, `all()`
**Sorting:** `sort()`, `sort_desc()`

#### ❌ Missing Array Methods

| Method | Ruby | Python | Description | Priority |
|--------|------|--------|-------------|----------|
| `compact()` | ✅ | ❌ | Remove nil/None values | HIGH |
| `rotate(n)` | ✅ | ❌ | Rotate elements by n positions | MEDIUM |
| `sample()` / `sample(n)` | ✅ | ❌ | Random element(s) | MEDIUM |
| `shuffle()` | ✅ | ❌ | Randomize order | MEDIUM |
| `transpose()` | ✅ | ❌ | Transpose 2D array | MEDIUM |
| `product(other)` | ✅ | ❌ | Cartesian product | LOW |
| `permutation(n)` | ✅ | ❌ | Generate permutations | LOW |
| `combination(n)` | ✅ | ❌ | Generate combinations | LOW |
| `bsearch()` | ✅ | ❌ | Binary search | LOW |
| `copy()` | ❌ | ✅ | Shallow copy (explicit) | LOW (already immutable) |
| `clear()` | ✅ | ✅ | Remove all elements | LOW (can use []) |
| `at(index)` | ✅ | ❌ | Get at index (with negative support) | LOW (have get) |
| `fetch(index, default)` | ✅ | ❌ | Get with default value | MEDIUM |
| `fill(value)` / `fill(start, count, value)` | ✅ | ❌ | Fill with value | LOW |
| `assoc(key)` | ✅ | ❌ | Find first subarray starting with key | LOW |
| `rassoc(value)` | ✅ | ❌ | Find first subarray with value at [1] | LOW |

### Dictionary/Hash Methods

#### ✅ Already Implemented in Simple

**Access:** `get()`, `get_or()`, `contains_key()`, `[key]`
**Mutation:** `set()`, `insert()`, `remove()`, `delete()`, `merge()`, `extend()`, `clear()`
**Inspection:** `len()`, `is_empty()`, `keys()`, `values()`, `entries()`, `items()`
**Transform:** `map_values()`, `filter()`

#### ❌ Missing Dictionary Methods

| Method | Ruby | Python | Description | Priority |
|--------|------|--------|-------------|----------|
| `setdefault(key, default)` | ❌ | ✅ | Get or set default value | MEDIUM |
| `popitem()` | ❌ | ✅ | Remove and return arbitrary (key, value) | LOW |
| `update(other)` | ✅ | ✅ | Merge other dict (mutating version) | LOW (have merge) |
| `fromkeys(keys, value)` | ❌ | ✅ | Create dict from keys with default value | MEDIUM |
| `fetch(key, default)` | ✅ | ❌ | Get with default, or raise if no default | MEDIUM |
| `dig(key1, key2, ...)` | ✅ | ❌ | Navigate nested structures safely | MEDIUM |
| `invert()` | ✅ | ❌ | Swap keys and values | LOW |
| `transform_keys()` | ✅ | ❌ | Map over keys | LOW |
| `transform_values()` | ✅ | ❌ | Map over values (have map_values) | LOW (have it) |
| `compact()` | ✅ | ❌ | Remove nil values | MEDIUM |

### Set Methods

#### ✅ Already Implemented in Simple

**Core:** `add()`, `remove()`, `contains()`, `size()`, `len()`, `is_empty()`, `clear()`
**Set Algebra:** `union()`, `intersection()`, `difference()`, `symmetric_difference()`, `is_subset()`, `is_superset()`, `is_disjoint()`
**Conversion:** `to_array()`, `to_list()`

#### ❌ Missing Set Methods

| Method | Ruby | Python | Description | Priority |
|--------|------|--------|-------------|----------|
| `update(other)` | ✅ | ✅ | Add all elements from other (mutating) | LOW |
| `intersection_update(other)` | ❌ | ✅ | Keep only elements in both (mutating) | LOW |
| `difference_update(other)` | ❌ | ✅ | Remove elements in other (mutating) | LOW |
| `symmetric_difference_update()` | ❌ | ✅ | Update with symmetric difference | LOW |
| `issubset()` | ❌ | ✅ | Alias for is_subset | LOW (alias) |
| `issuperset()` | ❌ | ✅ | Alias for is_superset | LOW (alias) |
| `isdisjoint()` | ❌ | ✅ | Alias for is_disjoint | LOW (alias) |

---

## Summary of High-Priority Missing Methods

### Strings (HIGH Priority)
1. `capitalize()` - Uppercase first, lowercase rest
2. `removeprefix(prefix)` - Remove prefix if present
3. `removesuffix(suffix)` - Remove suffix if present

### Numbers (HIGH Priority)
1. `gcd(other)` - Greatest common divisor (Integer)
2. `lcm(other)` - Least common multiple (Integer)

### Collections (HIGH Priority)
1. `compact()` - Remove nil values from arrays

### Strings (MEDIUM Priority)
- `swapcase()`, `title()`, `center()`, `zfill()`, `partition()`, `rpartition()`, `chomp()`, `squeeze()`

### Numbers (MEDIUM Priority)
- `digits(base)`, `bit_length()`, `chr()`, `is_integer()` (float), `as_integer_ratio()` (float)

### Collections (MEDIUM Priority)
- `rotate()`, `sample()`, `shuffle()`, `transpose()`, `fetch()`, `setdefault()`, `fromkeys()`, `dig()`, `compact()` (dict)

---

## Implementation Plan

### Phase 1: High-Priority Methods
1. String: `capitalize()`, `removeprefix()`, `removesuffix()`
2. Integer: `gcd()`, `lcm()`
3. Array: `compact()`

### Phase 2: Medium-Priority Methods
1. String: `swapcase()`, `title()`, `center()`, `zfill()`, `partition()`, `rpartition()`, `chomp()`, `squeeze()`
2. Integer: `digits()`, `bit_length()`, `chr()`
3. Float: `is_integer()`, `as_integer_ratio()`
4. Array: `rotate()`, `sample()`, `shuffle()`, `transpose()`, `fetch()`
5. Dict: `setdefault()`, `fromkeys()`, `dig()`, `compact()`

### Phase 3: Low-Priority Methods (Optional)
- Aliases and rarely-used methods
- Advanced combinatorial methods (permutation, combination, product)
- Bitwise predicate methods (allbits, anybits, nobits)

---

## Notes

- Simple already has a very comprehensive API
- Many "missing" methods are actually present with different names (e.g., `to_upper` vs `upcase`)
- Focus on adding methods that fill gaps, not duplicating functionality with aliases
- Prioritize methods that appear in both Ruby and Python
- Consider Simple's functional/immutable design when implementing mutating methods
