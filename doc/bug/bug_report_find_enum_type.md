# Bug Report: `.find()` Returns Enum Type in Interpreter

**Date:** 2026-03-14
**Severity:** Medium
**Component:** Interpreter (`src/compiler/95.interp/`)
**Feature:** doc_ref_lint (PDOC002-005 blocked)

## Summary

`.find()` on text returns an Option/enum type in interpreter mode instead of plain `i64`. This causes "semantic: type mismatch: cannot convert enum to int" when the result is compared (`>= 0`, `< 0`) or used in arithmetic (`pos + len`), but only in nested scopes (2+ levels of `if`/`while`/`for`).

## Reproduction

```simple
# WORKS — .find() used for .slice() without comparison (depth 2: while > if)
fn works(source: text) -> text:
    val lines = source.split("\n")
    var line_idx = 0
    while line_idx < lines.len():
        val line = lines[line_idx]
        if line.starts_with("fn "):
            val after = line.slice(3)
            val p = after.find("(")        # p is used directly
            val name = after.slice(0, p)   # works — no comparison
            return name
        line_idx = line_idx + 1
    ""

# FAILS — .find() result compared with >= 0 (same depth)
fn fails(source: text) -> text:
    val lines = source.split("\n")
    var line_idx = 0
    while line_idx < lines.len():
        val line = lines[line_idx]
        if line.starts_with("fn "):
            val after = line.slice(3)
            val p = after.find("(")
            if p >= 0:                     # ERROR: cannot convert enum to int
                return after.slice(0, p)
        line_idx = line_idx + 1
    ""

# FAILS — .find() in helper function called from nested scope
fn helper(s: text) -> text:
    val p = s.find("(")
    if p >= 0:                             # ERROR when called from nested scope
        return s.slice(0, p)
    s

fn also_fails(source: text) -> text:
    val lines = source.split("\n")
    for line in lines:
        if line.starts_with("fn "):
            return helper(line.slice(3))   # triggers error in helper
    ""
```

## Additional Finding: `.slice(i, i + computed)` Broken

Two-argument `.slice()` with computed variable indices returns wrong results:

```simple
# Returns wrong position (3 instead of 6)
fn broken_index_of(s: text, target: text) -> i64:
    var i = 0
    while i < s.len():
        if s.slice(i, i + target.len()) == target:  # wrong result
            return i
        i = i + 1
    -1

# Workaround: use .slice(i).starts_with(target)
fn working_index_of(s: text, target: text) -> i64:
    var i = 0
    while i < s.len():
        val sub = s.slice(i)
        if sub.starts_with(target):                  # correct
            return i
        i = i + 1
    -1
```

## Workarounds

1. **Use `.contains()` for boolean checks** instead of `.find() >= 0`
2. **Use `.find()` only for position extraction** without comparison — `val p = s.find("("); s.slice(0, p)`
3. **Custom `index_of` function** using `.slice(i).starts_with(target)` returns plain `i64`
4. **Keep `.find()` at minimal nesting depth** (while > if = 2 levels max)
5. **Avoid `.slice(i, i + computed)`** — use `.slice(i).starts_with()` or `.slice(i).slice(0, len)`

## Impact

- PDOC002-005 lint rules implemented but cannot be tested in interpreter mode
- Any text-scanning code using `.find()` with comparisons in nested scopes is affected
- Compiled mode is NOT affected (`.find()` returns `i64` correctly)

## Root Cause (Suspected)

The interpreter's type system wraps `.find()` return in `Option<i64>` (an enum with `Some(i64)` / `None` variants). At shallow nesting, the interpreter auto-unwraps. At deeper nesting, auto-unwrap fails, exposing the raw enum type which cannot be compared with `i64`.

## Related Files

- `src/compiler/35.semantics/lint/public_doc.spl` — workarounds applied
- `src/compiler/95.interp/` — interpreter implementation (likely fix location)
