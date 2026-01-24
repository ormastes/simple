# Simple Language Primitives Analysis
## Comparison with Ruby and Python Utility Functions

**Last updated**: 2026-01-24

Based on the Simple language specification and README, this analysis identifies missing utility functions compared to Ruby and Python's rich standard libraries, and evaluates whether Simple follows Ruby's "simple and short functions" philosophy.

**Naming Convention**: Simple uses **predicate methods without `?` suffix** (e.g., `empty` not `empty?`). This keeps parsing simple while maintaining Ruby-like brevity.

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
| Byte strings | ❌ Not implemented | `b"bytes"` |
| For-else | ❌ Not implemented | `for x in lst: else:` |
| Pipeline `\|>` | ❌ Not implemented | Use method chaining |

**Key finding**: Most grammar features are already implemented. Main gaps are in **stdlib methods** (string, number, collection utilities).

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

### Missing Functions - Consolidated Table

| Method | Description | Ruby | Python | Simple |
|--------|-------------|------|--------|--------|
| `len` / `size` | Get length | `size` | `len()` | ❌ |
| `empty` | Check if empty | `empty?` | `not s` | ❌ |
| `trim` | Strip whitespace | `strip` | `strip()` | ❌ |
| `ltrim` / `rtrim` | Strip left/right | `lstrip/rstrip` | `lstrip/rstrip` | ❌ |
| `up` | Uppercase | `upcase` | `upper()` | ❌ |
| `down` | Lowercase | `downcase` | `lower()` | ❌ |
| `capitalize` | Title first char | `capitalize` | `capitalize()` | ❌ |
| `rev` | Reverse string | `reverse` | `[::-1]` | ❌ |
| `split` | Split by separator | `split` | `split()` | ❌ |
| `join` | Join array to string | `join` | `join()` | ❌ |
| `replace` | Replace substring | `gsub` | `replace()` | ❌ |
| `find` | Find first index | `index` | `find()` | ⚠️ |
| `rfind` | Find last index | `rindex` | `rfind()` | ❌ |
| `contains` | Check substring | `include?` | `in` | ❌ |
| `starts_with` | Prefix check | `start_with?` | `startswith()` | ❌ |
| `ends_with` | Suffix check | `end_with?` | `endswith()` | ❌ |
| `count` | Count occurrences | `count` | `count()` | ❌ |
| `repeat` | Repeat n times | `*` | `*` | ❌ |
| `chars` | Char iterator | `chars` | `list(s)` | ❌ |
| `lines` | Line iterator | `lines` | `splitlines()` | ❌ |
| `bytes` | Byte view | `bytes` | `encode()` | ❌ |
| `to_int` | Parse to int | `to_i` | `int()` | ❌ |
| `to_float` | Parse to float | `to_f` | `float()` | ❌ |
| `is_digit` | All digits? | - | `isdigit()` | ❌ |
| `is_alpha` | All letters? | - | `isalpha()` | ❌ |
| `center` | Center pad | `center` | `center()` | ❌ |
| `pad_left` | Left pad | `ljust` | `ljust()` | ❌ |
| `pad_right` | Right pad | `rjust` | `rjust()` | ❌ |

### Recommended Simple String API
```simple
# Short, chainable names (no ? suffix)
s.len           # length
s.empty         # is empty (predicate, no ?)
s.trim          # strip whitespace
s.up            # uppercase
s.down          # lowercase
s.rev           # reverse
s.split(",")    # split by separator
s.replace("a", "b")  # replace all
s.contains("x") # substring check
s.starts_with("http")
s.ends_with(".txt")

# Chainable
name.trim.down.split(",").map(\x: x.trim)
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

### Missing Functions - Consolidated Table

| Method | Description | Ruby | Python | Simple |
|--------|-------------|------|--------|--------|
| `abs` | Absolute value | `abs` | `abs()` | ❌ |
| `floor` | Round down | `floor` | `math.floor()` | ❌ |
| `ceil` | Round up | `ceil` | `math.ceil()` | ❌ |
| `round` | Round to digits | `round` | `round()` | ❌ |
| `trunc` | Truncate | `truncate` | `math.trunc()` | ❌ |
| `clamp` | Clamp to range | `clamp` | - | ❌ |
| `sign` | Get sign (-1,0,1) | - | - | ❌ |
| `divmod` | Div + mod tuple | `divmod` | `divmod()` | ❌ |
| `pow` | Power | `**` | `pow()` | ⚠️ Operator? |
| `sqrt` | Square root | `Math.sqrt` | `math.sqrt()` | ⚠️ Math module |
| `even` | Is even | `even?` | `% 2 == 0` | ❌ |
| `odd` | Is odd | `odd?` | `% 2 == 1` | ❌ |
| `positive` | Is > 0 | `positive?` | `> 0` | ❌ |
| `negative` | Is < 0 | `negative?` | `< 0` | ❌ |
| `zero` | Is == 0 | `zero?` | `== 0` | ❌ |
| `between` | In range | `between?` | - | ❌ |
| `is_nan` | Is NaN (float) | `nan?` | `math.isnan()` | ❌ |
| `is_inf` | Is infinite | `infinite?` | `math.isinf()` | ❌ |
| `to_string` | Convert to string | `to_s` | `str()` | ❌ |
| `to_int` | Convert to int | `to_i` | `int()` | ❌ |
| `to_float` | Convert to float | `to_f` | `float()` | ❌ |
| `bit_len` | Bit length | `bit_length` | `bit_length()` | ❌ |
| `popcount` | Count 1 bits | `digits(2).sum` | `bin().count('1')` | ❌ |

### Inconsistency Traps to Avoid
- **`mod` sign rules**: Python's `%` is always non-negative; C/Ruby can be negative. Pick one and document.
- **`round` ties**: Ties-to-even vs ties-away-from-zero. Pick one.

### Recommended Simple Number API
```simple
# Short predicate names (no ? suffix)
n.abs
n.floor
n.ceil
n.round(2)      # round to 2 decimal places
n.clamp(0, 100) # clamp to range
n.even          # is even (no ?)
n.odd           # is odd (no ?)
n.positive      # is > 0 (no ?)
n.negative      # is < 0 (no ?)
n.zero          # is == 0 (no ?)

# Chainable
x.abs.clamp(0, 10).to_string
```

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

### Vec/Array - Missing Functions

| Method | Description | Ruby | Python | Simple |
|--------|-------------|------|--------|--------|
| `len` | Get length | `size` | `len()` | ❌ |
| `empty` | Is empty | `empty?` | `not lst` | ❌ |
| `push` | Add to end | `push` | `append()` | ❌ |
| `pop` | Remove from end | `pop` | `pop()` | ❌ |
| `insert` | Insert at index | `insert` | `insert()` | ❌ |
| `remove_at` | Remove at index | `delete_at` | `pop(i)` | ❌ |
| `clear` | Remove all | `clear` | `clear()` | ❌ |
| `first` | First element | `first` | `[0]` | ❌ |
| `last` | Last element | `last` | `[-1]` | ❌ |
| `take` | First n elements | `take` | `[:n]` | ❌ |
| `drop` | Skip first n | `drop` | `[n:]` | ❌ |
| `slice` | Subarray | `slice` | `[a:b]` | ⚠️ |
| `concat` | Join arrays | `concat` | `extend()` | ❌ |
| `rev` | Reverse order | `reverse` | `reverse()` | ❌ |
| `sort` | Sort elements | `sort` | `sort()` | ⚠️ Mentioned |
| `sort_by` | Sort by key | `sort_by` | `sorted(key=)` | ❌ |
| `uniq` | Remove duplicates | `uniq` | `set()` | ❌ |
| `flat` | Flatten nested | `flatten` | - | ❌ |
| `compact` | Remove nils | `compact` | - | ❌ |
| `shuffle` | Random order | `shuffle` | `random.shuffle` | ❌ |
| `sample` | Random element(s) | `sample` | `random.choice` | ❌ |
| `min` | Minimum element | `min` | `min()` | ❌ |
| `max` | Maximum element | `max` | `max()` | ❌ |
| `sum` | Sum all elements | `sum` | `sum()` | ❌ |
| `contains` | Check membership | `include?` | `in` | ❌ |
| `index` | Find position | `index` | `index()` | ❌ |
| `count` | Count matches | `count` | `count()` | ❌ |
| `join` | Join to string | `join` | `join()` | ❌ |

### Dict/Map - Missing Functions

| Method | Description | Ruby | Python | Simple |
|--------|-------------|------|--------|--------|
| `len` | Number of entries | `size` | `len()` | ❌ |
| `empty` | Is empty | `empty?` | `not d` | ❌ |
| `get` | Get with default | `fetch` | `get()` | ❌ |
| `set` | Set value | `[]=` | `[]=` | ⚠️ |
| `remove` | Delete key | `delete` | `del` | ❌ |
| `contains_key` | Has key | `has_key?` | `in` | ❌ |
| `contains_value` | Has value | `has_value?` | `in values()` | ❌ |
| `keys` | All keys | `keys` | `keys()` | ❌ |
| `values` | All values | `values` | `values()` | ❌ |
| `items` | Key-value pairs | `to_a` | `items()` | ❌ |
| `merge` | Combine dicts | `merge` | `\|` | ❌ |
| `invert` | Swap keys/values | `invert` | - | ❌ |
| `select` | Filter by predicate | `select` | - | ❌ |
| `transform_keys` | Map over keys | `transform_keys` | - | ❌ |
| `transform_values` | Map over values | `transform_values` | - | ❌ |
| `dig` | Nested access | `dig` | - | ❌ |

### Set - Missing Functions

| Method | Description | Ruby | Python | Simple |
|--------|-------------|------|--------|--------|
| `len` | Size | `size` | `len()` | ❌ |
| `empty` | Is empty | `empty?` | `not s` | ❌ |
| `add` | Add element | `add` | `add()` | ❌ |
| `remove` | Remove element | `delete` | `remove()` | ❌ |
| `contains` | Has element | `include?` | `in` | ❌ |
| `union` | Set union | `\|` | `\|` | ❌ |
| `intersect` | Set intersection | `&` | `&` | ❌ |
| `diff` | Set difference | `-` | `-` | ❌ |
| `symmetric_diff` | XOR | `^` | `^` | ❌ |
| `subset` | Is subset | `subset?` | `<=` | ❌ |
| `superset` | Is superset | `superset?` | `>=` | ❌ |

### Recommended Simple Collections API
```simple
# Vec - short names, no ? suffix
v.len
v.empty           # predicate (no ?)
v.first
v.last
v.push(x)
v.pop
v.take(3)
v.drop(3)
v.rev
v.sort
v.uniq
v.contains(x)     # predicate (no ?)

# Iteration pipeline (critical for Ruby feel)
data
    .filter(\x: x > 0)
    .map(\x: x * 2)
    .group_by(\x: x % 10)
    .items
    .sort_by(\k, v: k)

# Dict
d.get("key", default)
d.keys
d.values
d.items
d.contains_key("k")
d.merge(other)

# Boolean aggregation (no ? suffix)
lst.any(\x: x > 10)   # any match?
lst.all(\x: x > 0)    # all match?
lst.none(\x: x < 0)   # none match?
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

### Missing Functions - Consolidated Table

| Method | Description | Ruby | Python | Simple |
|--------|-------------|------|--------|--------|
| `File.read` | Read entire file | `File.read` | `open().read()` | ❌ |
| `File.write` | Write entire file | `File.write` | `open().write()` | ❌ |
| `File.lines` | Read as line array | `File.readlines` | `readlines()` | ❌ |
| `File.append` | Append to file | mode `'a'` | mode `'a'` | ❌ |
| `File.read_bytes` | Read binary | mode `'rb'` | mode `'rb'` | ❌ |
| `File.write_bytes` | Write binary | mode `'wb'` | mode `'wb'` | ❌ |
| `File.exists` | Check exists | `File.exist?` | `os.path.exists()` | ❌ |
| `File.is_file` | Is regular file | `File.file?` | `os.path.isfile()` | ❌ |
| `File.is_dir` | Is directory | `File.directory?` | `os.path.isdir()` | ❌ |
| `File.size` | Get file size | `File.size` | `os.path.getsize()` | ❌ |
| `File.delete` | Delete file | `File.delete` | `os.remove()` | ❌ |
| `File.rename` | Rename file | `File.rename` | `os.rename()` | ❌ |
| `File.copy` | Copy file | `FileUtils.cp` | `shutil.copy()` | ❌ |
| `File.move` | Move file | `FileUtils.mv` | `shutil.move()` | ❌ |
| `f.read` | Read from handle | `read` | `read()` | ❌ |
| `f.write` | Write to handle | `write` | `write()` | ❌ |
| `f.each_line` | Line iterator | `each_line` | `for line in f` | ❌ |
| `f.seek` | Set position | `seek` | `seek()` | ❌ |
| `f.tell` | Get position | `pos` | `tell()` | ❌ |
| `f.flush` | Flush buffer | `flush` | `flush()` | ❌ |
| `f.close` | Close handle | `close` | `close()` | ❌ |
| `f.eof` | At end of file | `eof?` | - | ❌ |

### Path Module - Missing Functions

| Method | Description | Ruby | Python | Simple |
|--------|-------------|------|--------|--------|
| `Path.join` | Join path parts | `File.join` | `os.path.join()` | ❌ |
| `Path.dirname` | Directory part | `File.dirname` | `os.path.dirname()` | ❌ |
| `Path.basename` | Filename part | `File.basename` | `os.path.basename()` | ❌ |
| `Path.ext` | Extension | `File.extname` | `os.path.splitext()` | ❌ |
| `Path.stem` | Name without ext | - | `Path().stem` | ❌ |
| `Path.normalize` | Normalize path | `File.expand_path` | `os.path.normpath()` | ❌ |
| `Path.absolute` | Absolute path | `File.expand_path` | `os.path.abspath()` | ❌ |
| `Path.relative` | Relative path | - | `os.path.relpath()` | ❌ |
| `Path.parent` | Parent directory | `File.dirname` | `Path().parent` | ❌ |

### Directory Module - Missing Functions

| Method | Description | Ruby | Python | Simple |
|--------|-------------|------|--------|--------|
| `Dir.list` | List directory | `Dir.entries` | `os.listdir()` | ❌ |
| `Dir.glob` | Pattern matching | `Dir.glob` | `glob.glob()` | ❌ |
| `Dir.walk` | Recursive walk | - | `os.walk()` | ❌ |
| `Dir.mkdir` | Create directory | `Dir.mkdir` | `os.mkdir()` | ❌ |
| `Dir.mkdir_p` | Create with parents | `FileUtils.mkdir_p` | `os.makedirs()` | ❌ |
| `Dir.rmdir` | Remove directory | `Dir.rmdir` | `os.rmdir()` | ❌ |
| `Dir.rm_rf` | Remove recursive | `FileUtils.rm_rf` | `shutil.rmtree()` | ❌ |
| `Dir.exists` | Check exists | `Dir.exist?` | `os.path.isdir()` | ❌ |
| `Dir.cwd` | Current directory | `Dir.pwd` | `os.getcwd()` | ❌ |
| `Dir.chdir` | Change directory | `Dir.chdir` | `os.chdir()` | ❌ |

### Inconsistency Trap to Avoid
- Splitting "file" and "path" modules requires verbose imports for common tasks
- Solution: Make path operations available both as `Path.join()` and `File.join()`

### Recommended Simple File/Path API
```simple
# One-liner convenience (CRITICAL)
content = File.read("data.txt")
File.write("out.txt", content)
lines = File.lines("data.txt")

# Predicates (no ? suffix)
File.exists("data.txt")
File.is_dir("/path")
File.is_file("/path")

# Path operations
path = Path.join("dir", "subdir", "file.txt")
dir = Path.dirname(path)
name = Path.basename(path)
ext = Path.ext(path)          # => ".txt"

# Directory operations
files = Dir.list("/path")
matches = Dir.glob("*.txt")

# Block-based safe close
File.open("data.txt") \f:
    for line in f.each_line:
        process(line)
```

---

## 5. Identified Inconsistencies & Gaps

### 5.1 Naming Consistency Strategy

**Recommended approach**: Pick ONE canonical name, document it, use it consistently in examples.

| Concept | Option A | Option B | Simple Recommendation |
|---------|----------|----------|----------------------|
| Length | `len` (Python) | `size` (Ruby) | `len` (shorter) |
| Add to end | `push` (Ruby) | `append` (Python) | `push` (shorter) |
| Whitespace trim | `trim` | `strip` | `trim` (more universal) |
| Uppercase | `up` | `upper` | `up` (shorter) |
| Lowercase | `down` | `lower` | `down` (shorter) |
| Reverse | `rev` | `reverse` | `rev` (shorter) |
| Substring check | `contains` | `has` | `contains` (clearer) |
| Empty check | `empty` | `is_empty` | `empty` (shorter) |

### 5.2 Predicate Naming (No `?` Suffix)

Simple uses predicates **without** the `?` suffix for simpler parsing:

```simple
# Recommended (no ? suffix)
s.empty         # not empty?
n.even          # not even?
lst.contains(x) # not contains?(x)
File.exists(p)  # not exists?(p)

# Predicates read naturally without ?
if s.empty:
    print "string is empty"

if n.even:
    print "number is even"
```

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
| **Predicate naming** | All predicates: no `?`, no `is_` prefix |

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
| `fn f() -> Int?` | **type system** | Needs type system |
| `extend String` | **type system** | Needs type system |
| `yield x` generators | **parser + runtime** | Needs parser + runtime |
| `with file as f:` | ~~parser + runtime protocol~~ | ✅ **Implemented** (parser done)

---

## 12. Final Summary

**Last updated**: 2026-01-24

### Implementation Breakdown

| Category | Count | Status |
|----------|-------|--------|
| **API/Stdlib Only** | ~80 methods | Needs implementation |
| **Grammar/Parser** | ~20 features | ✅ **17 implemented**, 4 remaining |
| **Type System** | ~6 features | Needs implementation |
| **Runtime** | ~4 features | Partial (context managers have parser support) |

### Grammar Features Status Summary

| Status | Count | Features |
|--------|-------|----------|
| ✅ Implemented | 17 | `?.`, `??`, `[a:b]`, `[-1]`, `...spread`, comprehensions, `with`, destructuring, guards, chained comparisons, ranges, named args, defaults, variadic, raw strings, interpolation |
| ⚠️ Partial | 3 | Range step (slice only), regex (`"re"_re`), multiple assignment (via destructuring) |
| ❌ Missing | 4 | Byte strings, for-else, elvis `?:`, pipeline `\|>` |

### What Makes Ruby Feel "Short"

1. **Unified iteration** - Same methods on all collections ⚠️ Need Iterable trait stdlib
2. **One-liner file ops** - `File.read(path)` ⚠️ Need stdlib
3. **Chainable everything** - `->` operator ✅ Already exists
4. **Short names** - `len`, `rev`, `up` ⚠️ Need stdlib naming
5. **Slice syntax** - `[1:5]`, `[-1]` ✅ **Implemented**
6. **Safe nil handling** - `?.` operator ✅ **Implemented**

### Recommended Order (Updated)

1. **First** (Stdlib): String/Number/Collection methods - biggest bang for buck
2. **Second** (Type System): Optional `T?` sugar, extension methods
3. **Third** (Runtime): Lazy iterators, context manager protocol
4. **Later** (Grammar): Byte strings, for-else (low priority)

### Naming Convention (Established)

```simple
# Predicates: no ? suffix, no is_ prefix
empty, even, odd, positive, contains, exists

# Short names preferred
len, rev, up, down, trim

# Consistent across types
Vec.len, String.len, Dict.len  # not size vs length vs count
```
