# Array `.at(i)` is a bounds-checked Option accessor, not an alias for `[i]`

`.at(i)` returns `Some(element)` for an in-range index and `None` otherwise. It is *not* the same operation as `[i]`: `[i]` yields the element directly and has no way to report absence, while `.at(i)` is the safe accessor that ~161 call sites across the tree consume with `match`/`unwrap`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib / collection accessors |
| Source | `test/01_unit/lib/common/array_at_option_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple sspec-docgen` (Rust) |

**Bug:** doc/08_tracking/bug/array_at_returns_nil_for_every_index_2026-08-01.md

## Overview

`.at(i)` returns `Some(element)` for an in-range index and `None` otherwise. It
is *not* the same operation as `[i]`: `[i]` yields the element directly and has
no way to report absence, while `.at(i)` is the safe accessor that ~161 call
sites across the tree consume with `match`/`unwrap`.

Before the fix the Rust seed had no array `at` at all — only the *text* one
(`"char_at" | "at" => rt_string_char_at`). Every `arr.at(i)` therefore fell
through the unhandled-method path to `Value::Nil`, which reads as `None`. That
is the same value a genuinely out-of-range read produces, so every in-range hit
silently took the `None` branch with no error and no crash.

That failure shape is why the in-range assertions below matter more than the
out-of-range ones. `at(99) == None` passed even when `.at()` was completely
unimplemented; only `at(0) == Some(10)` can tell the two apart. Each in-range
assertion here is RED against the unpatched seed.

## Coverage

- in-range hit (first, interior, and the `len - 1` boundary)
- out-of-range: `len` exactly, and far past the end
- negative index — must be `None`, never a wrap-around to a huge positive index
- empty container
- index 3 specifically, and the *element value* 3, because the nil sentinel is 3
- `.at()` against `[i]` on the same array, so the two cannot silently diverge

## Syntax

```simple
match xs.at(0):
    Some(v): v
    None: -1
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/01_unit/lib/common/array_at_option/result.json` |
