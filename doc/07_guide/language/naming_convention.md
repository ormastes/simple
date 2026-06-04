# Simple Language Naming Convention Guide

**Canonical reference.** This document supersedes the naming table in
`coding_style.md` and consolidates the verb families, alias policy, and
predicate gate from `doc/01_research/lib/best_practices/naming.md`.

---

## 1. Module & Directory Naming

All module names are `snake_case`. Prefer short, conventional abbreviations —
they match import paths that are already dominant in the test corpus.

| Short form | What it contains |
|---|---|
| `fs` | High-level filesystem API (public surface) |
| `fs_driver` | VFS driver layer (different concern from `fs`) |
| `db` | Storage engine (pager, B-tree, WAL) |
| `net` | TCP/UDP/HTTP networking |
| `compress` | Compression API facade |
| `spec` | Test DSL (spipe/spec) |
| `text` | String/text type and utilities (`string` is legacy alias) |
| `crypto` | Cryptographic primitives |
| `math` | Numeric and algebraic utilities |
| `io` | I/O primitives |
| `ffi` | C/native bindings |

Some modules have a paired long-form directory that serves a **different
architectural role** (not a duplicate):

| Short name (API) | Long name (impl/layer) | Distinction |
|---|---|---|
| `fs/` | `file_system/` | `file_system/` = legacy mock/compat shim |
| `db/` | `database/` | `database/` = app-layer SQL, FTS, migrations |
| `compress/` | `compression/` | `compression/` = codec internals (gzip, brotli, lz4) |
| `spec/` | `testing/`, `test/` | `testing/` = internal helpers/mocks, `test/` = fixtures |

Do NOT merge these pairs. See `doc/07_guide/language/lib_architecture.md` §5.

**Rule:** when adding a new module, pick the shortest common abbreviation used
in the field. If no abbreviation is universally understood, use the full word.
Never invent a new abbreviation that has no precedent.

---

## 2. Function & Method Naming

All function and method names are `snake_case`.

### Drop `get_` for accessors

Bare noun methods are the canonical form. Remove `get_` everywhere:

| Avoid | Prefer |
|---|---|
| `get_extension(path)` | `extension(path)` |
| `get_stem(path)` | `stem(path)` |
| `get_parent_dir(path)` | `parent_dir(path)` |
| `get_dir_name(path)` | `dir_name(path)` |
| `get_host_os()` | `host_os()` |
| `get_exit_code()` | `exit_code()` |
| `get_container()` | `container()` |

Exception: `register_*`, `fetch_*`, `set_from_list` — these carry semantic load
beyond mere access and keep their prefix.

### Canonical Verb Families

One canonical verb per operation. Aliases are allowed only when they forward to
the canonical implementation (see §5).

| Operation | Preferred | Avoid |
|---|---|---|
| Iterate for side effects | `each` | `for_each_item`, `iterate_all` |
| Transform | `map` | `transform_values` |
| Filter keep | `select` | `filter_true`, `where_all` |
| Filter drop | `reject` | `filter_not` |
| Fold/accumulate | `reduce` | `inject`, `fold_left` |
| Flatten + map | `flat_map` | `collect_concat` |
| First match | `find` | `search_for_one` |
| Index/key (required) | `fetch` | `get_or_fail` |
| Index/key (optional) | `get`, `at` | `maybe_get_value` |
| Append one | `push`, `append` | `add_item_to_end` |
| Append many | `extend`, `concat` | `append_all_items` |
| Membership test | `include?` | `has_member`, `contains_item` |
| Head/tail | `first`, `last` | `head`, `tail` |
| Slice from front | `take` | `take_first_n` |
| Slice from back | `drop` | `skip` |
| Count matching | `count` | `count_where` |
| Short-circuit all | `all?` | `every`, `all_match` |
| Short-circuit any | `any?` | `some`, `exists` |
| Short-circuit none | `none?` | `not_any` |
| String conversion | `to_string`, `as_str` | `stringify`, `str_value` |
| Parsing | `parse`, `try_parse` | `from_string_maybe` |
| Validation | `validate`, `check` | `do_validation` |
| Pairing across collections | `zip` | `zip_with_index` (use `zip` + `each_with_index`) |

### Conversion Prefixes

| Prefix | Semantics |
|---|---|
| `to_*` | Allocates or produces a new value (`path.to_string()`) |
| `as_*` | Cheap borrowed or view-like access — no allocation (`slice.as_bytes()`) |
| `into_*` | Consumes or transfers ownership (`buffer.into_text()`) |
| `try_*` | Fallible fast-path where failure is expected and non-exceptional |

---

## 3. Predicate Naming

### New public APIs: use `.?` postfix

Simple's `.?` postfix predicate is ergonomically closest to Ruby's `?` suffix
and is the canonical form for all new public APIs:

```simple
arr.empty.?
path.valid.?
user.present.?
text.blank.?
```

### Legacy `is_*` / `has_*`

These are **advisory debt** — never grow them. Migrate callers when a file is
being touched anyway. The enforcement baseline lives in
`scripts/audit/api_consistency_baseline.json`; the audit script fails if
predicate-prefix counts grow.

### Free-standing predicates (no receiver)

Free-standing predicates (no `self`) remain as `is_*` because the `.?` postfix
form requires a receiver:

```simple
is_windows()
is_debug_build()
is_little_endian()
```

---

## 4. Type & Trait Naming

| Item | Convention | Example |
|---|---|---|
| Classes, Structs, Enums | PascalCase | `HttpClient`, `ParseError` |
| Traits | PascalCase, no `I` prefix | `Readable`, `Serializable` |
| Constants | SCREAMING_CASE | `MAX_RETRIES`, `DEFAULT_PORT` |
| Type parameters | Single uppercase or short PascalCase | `T`, `K`, `V`, `Elem` |

No `I` prefix for traits — Simple is not Java. Traits describe a capability;
the name is the capability: `Readable`, `Writable`, `Closeable`, `Iterable`.

---

## 5. Alias Policy

Ruby-inspired aliases are allowed when **all four** conditions hold:

1. The alias is common enough to reduce real call-site noise.
2. The alias forwards to exactly one canonical implementation — no duplicated behavior.
3. Documentation names the canonical method, not the alias.
4. Tests cover canonical behavior; alias tests only verify delegation.

**Allowed examples:** `each → iter`, `select → filter`, `empty.? → is_empty`
(compatibility bridge during migration).

**Rejected:** aliases that only reorder words, duplicate behavior, or hide
different failure semantics.

### Deprecation Pattern

```simple
@deprecated("use extension(path) instead")
fn get_extension(path: Path) -> text {
    extension(path)
}
```

Use `type` for type-level renaming:

```simple
type Buf = Buffer   # type alias — same underlying type
alias OldName = NewName  # class rename at module boundary
```

---

## 6. Mutation & Side-Effect Naming

| Pattern | Rule | Example |
|---|---|---|
| Mutating method | `_in_place` suffix unless type is builder/stream/session/handle/cursor/buffer | `sort_in_place()`, `reverse_in_place()` |
| Blocking call | `blocking_` prefix when async alternative exists | `blocking_read()`, `blocking_connect()` |
| Fallible operation | Use verbs that imply failure (`parse`, `open`, `read`, `decode`, `compile`) — return `Result<T, E>` | `parse(text)`, `open(path)` |
| Builder/session | No suffix needed — mutation is the type's contract | `builder.add(x).build()` |
| Null-aware variants | `_or_null` suffix or `?` return type rather than overloading base name | `first_or_null()`, `min_or_null()` |

**Do not hide failure behind nullable returns.** Fallible operations must return
`Result<T, E>` and use verbs that semantically signal fallibility.

---

## 7. Private Members

Private items use a `_` prefix:

```simple
class Parser {
    _position: i32
    _tokens: [Token]

    fn _advance() { ... }
    fn parse() -> Ast { ... }  # public
}
```

Module-internal helpers that are not exported also use `_` prefix to signal
intent even when the language does not enforce visibility at the file level.

---

## Quick Reference

| Decision | Rule |
|---|---|
| Module name length | Shortest common abbreviation (`fs`, `db`, `net`) |
| Accessor prefix | None — bare noun (`extension`, not `get_extension`) |
| New predicate | `.?` postfix form |
| Existing `is_*` | Leave; migrate when touching the file |
| Free-standing predicate | `is_*` (no receiver) |
| Alias | Only if forwards to canonical and reduces noise |
| Mutation | `_in_place` suffix (except builder types) |
| Async/sync pair | `blocking_` prefix on sync variant |
| Allocating conversion | `to_*` |
| Cheap view | `as_*` |
| Consuming conversion | `into_*` |
| Fallible fast-path | `try_*` |
| Type/trait casing | PascalCase — no `I` prefix |
| Constants | SCREAMING_CASE |
| Private members | `_` prefix |
