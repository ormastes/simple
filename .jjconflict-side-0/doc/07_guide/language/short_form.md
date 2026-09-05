# Short-Form Coding in Simple

Simple aims for Ruby-like ergonomics: code should read like well-chosen prose, not
like a formal specification. Every word must earn its place.

---

## 1. Why Short Form?

Verbose names slow readers. Short, predictable names let you scan a method chain the
same way you scan a sentence. Simple provides syntax features — aliases, predicate
operators, no-paren calls, implicit return — to make the short form the path of least
resistance, not a workaround.

---

## 2. Cross-Language Comparison

These names are canonical across Ruby, Python, Kotlin, and Swift. Use them in Simple
without qualification — they carry zero learning cost from any ecosystem.

| Operation | Ruby | Python | Kotlin | Swift | Simple |
|-----------|------|--------|--------|-------|--------|
| Transform each | `map` | `map()` | `map {}` | `map` | `map` |
| Keep matching | `select`/`filter` | `filter()` | `filter {}` | `filter` | `filter` |
| Remove matching | `reject` | negate filter | `filterNot {}` | negate filter | `reject` |
| Flatten + map | `flat_map` | list comp | `flatMap {}` | `flatMap` | `flat_map` |
| Map, drop nils | `filter_map` | list comp | `mapNotNull {}` | `compactMap` | `compact_map` |
| Fold/accumulate | `inject`/`reduce` | `functools.reduce` | `fold`/`reduce` | `reduce` | `reduce` |
| Iterate (side fx) | `each` | `for` loop | `forEach {}` | `forEach` | `each` |
| Any match? | `any?` | `any()` | `any {}` | method | `any` |
| All match? | `all?` | `all()` | `all {}` | method | `all` |
| None match? | `none?` | `not any()` | `none {}` | method | `none` |
| Membership | `include?` | `in` | `contains` | `contains` | `contains` |
| Length | `size`/`length` | `len()` | `.size` | `.count` | `size` / `count` |
| Empty check | `empty?` | `not seq` | `isEmpty` | `isEmpty` | `empty.?` |
| First element | `first` | `seq[0]` | `first()` | `first` | `first` |
| Last element | `last` | `seq[-1]` | `last()` | `last` | `last` |
| Take N | `take` | `seq[:n]` | `take(n)` | `prefix(n)` | `take` |
| Drop N | `drop` | `seq[n:]` | `drop(n)` | `dropFirst(n)` | `drop` |
| Pair sequences | `zip` | `zip()` | `zip` | `zip` | `zip` |
| Group by key | `group_by` | `itertools.groupby` | `groupBy {}` | `Dictionary(grouping:)` | `group_by` |
| Sort (copy) | `sort` | `sorted()` | `sortedBy {}` | `sorted(by:)` | `sort` / `sorted` |
| Sort (in place) | `sort!` | `list.sort()` | `sortWith {}` | `sort(by:)` | `sort_in_place` |
| To string | `to_s` | `str()` | `toString()` | `String(...)` | `to_str` |
| Debug print | `p` / `pp` | `repr()` | — | — | `p` |
| Console output | `puts` | `print()` | `println()` | `print()` | `puts` |
| Join to string | `join` | `sep.join(seq)` | `joinToString()` | `joined(separator:)` | `join` |
| Split string | `split` | `str.split()` | `split()` | `split(separator:)` | `split` |
| Path extension | `File.extname` | `Path.suffix` | Java nio | `URL.pathExtension` | `.suffix` |
| Path stem | `File.basename(p,'.*')` | `Path.stem` | Java nio | `URL.deletingPathExtension` | `.stem` |
| Tap into chain | `tap` | — | `also {}` | — | `tap` |
| Pipeline step | `then`/`yield_self` | — | `let {}` | — | `then` |

---

## 3. Verbose → Short Cheat Sheet

| Verbose (avoid) | Short (prefer) | Why |
|---|---|---|
| `get_name()` | `name` | Bare noun — no `get_` prefix ever |
| `get_extension(path)` | `path.extension` or `path.suffix` | Property, not a getter |
| `is_empty()` | `list.empty.?` or `not list.?` | `.?` predicate form |
| `is_file()` | `file.?` | `.?` on receiver |
| `for_each_item(fn)` | `each(fn)` | Canonical verb |
| `filter_not(fn)` | `reject(fn)` | Ruby canonical |
| `get_or_fail(key)` | `fetch(key)` | Ruby canonical for key lookup |
| `filter_map(fn)` | `compact_map(fn)` | Explicit about nil removal |
| `map_not_null(fn)` | `compact_map(fn)` | Simple canonical |
| `file_read(path)` | `read(path)` | Short verb when context is clear |
| `to_string()` | `to_str` | No parens when no args |
| `is_valid()` | `valid.?` | Predicate property form |
| `forEach {}` | `each {}` | Simple canonical, not Kotlin |
| `getOrNull(key)` | `fetch?(key)` or first element of `get(key)` | Nullable access |

---

## 4. Alias Patterns

Aliases are compile-time: zero runtime overhead, no vtable entry, no indirection.

### Function alias — migration and canonical shorthand

```simple
# Expose a canonical short name for a longer implementation
fn map = transform_each

# Deprecate old name while keeping a stable target
@deprecated("Use map instead")
fn collect = map
```

Use when: adding a Ruby-canonical name to an existing method, or deprecating a
`get_`-prefixed name without breaking callers.

### Type alias — generic shorthand

```simple
type StringMap<V> = Map<text, V>
type Handler = fn(Event) -> ()
type Result<T> = Option<T>
```

Use when: a generic instantiation is used in many signatures and the parameterized
form clutters reading.

### Class alias — renaming without inheritance

```simple
alias Optional = Option
alias Vec = Vector
pub alias PublicPoint = InternalPoint
```

Use when: an internal name must be exported under a public-API name, or a stdlib
name should have a familiar alias for developers from another language.

### Deprecation workflow

```simple
# Step 1: implement under the new name
fn fetch(key: text) -> Option<text> { ... }

# Step 2: alias old name, mark deprecated
@deprecated("Use fetch instead")
fn get_or_fail = fetch

# Step 3: after one release cycle, delete get_or_fail
```

---

## 5. Predicate Short Forms

Simple's `.?` operator applies a boolean predicate without writing a named `is_*`
method.

### Basics

```simple
# From a boolean property named 'empty':
list.empty.?          # true if list.empty == true

# From a collection (truthy = non-empty):
list.?                # true if list is non-empty

# Negation:
not list.?            # true if list is empty
```

### Migration from `is_*`

| Old `is_*` form | New `.?` form | Notes |
|---|---|---|
| `result.is_ok()` | `result.ok.?` | property + predicate |
| `path.is_absolute()` | `path.absolute.?` | property + predicate |
| `file.is_empty()` | `file.empty.?` | property + predicate |
| `s.is_empty()` | `s.empty.?` | property + predicate |

### When `is_*` is still appropriate

Use `is_*` for free-standing functions with no natural receiver:

```simple
fn is_valid_identifier(s: text) -> bool { ... }
```

Do not use `is_*` as a method name on a type. Add an `empty`, `valid`, `absolute`
property and let callers use `.?`.

---

## 6. Method Call Sugar

### No-paren calls

Methods with no arguments may be called without parentheses:

```simple
path.stem          # instead of path.stem()
list.first         # instead of list.first()
user.name          # instead of user.name()
result.to_str      # instead of result.to_str()
```

Prefer the no-paren form for anything that reads as a property or noun.

### Implicit return

The last expression in a function body is the return value. No `return` keyword needed:

```simple
fn double(n: i64) -> i64 {
    n * 2           # returned automatically
}

fn describe(user: User) -> text {
    "name={user.name} age={user.age}"
}
```

Use explicit `return` only for early exit.

### Block / closure syntax

```simple
# Short block (single expression):
names.map { |n| n.upcase }

# Multi-line block:
items.each { |item|
    log(item)
    process(item)
}

# Tap — run side effects, return self:
config
    .tap { |c| log("loaded: {c.name}") }
    .validate

# Then — transform in a pipeline:
raw_text
    .then { |t| parse(t) }
    .then { |doc| render(doc) }
```

---

*Source research: `.spipe/lib-naming-consistency/research_cross_lang.md`*
