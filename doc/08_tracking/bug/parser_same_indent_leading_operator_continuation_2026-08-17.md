# Leading-operator line continuation at the SAME indent does not parse

**Date:** 2026-08-17
**Status:** OPEN
**Severity:** MEDIUM — `src/lib/nogc_async_mut/wm/wm_optimization.spl` (and every
module importing it) fails to parse
**Found by:** `src/lib/**` parse sweep (7780 files)
**Binary:** `/mnt/data/cgtw2/release/simple` (freshly built Rust seed) — also
fails on the stale deployed binary, so this is not a fresh-build regression

## Relationship to the existing record

`doc/08_tracking/bug/parser_leading_operator_line_continuation_2026-08-01.md` is
marked FIXED and its repro genuinely passes today. That fix covered the
continuation line being **more indented** than the first line. The **same-indent**
shape was never covered and still fails.

## Minimal reproduction

FAILS — continuation at the same indent as the head line:

```simple
fn a1(a: text) -> text:
    "x" + a
    + "y"
```

```
error: compile failed: parse: Unexpected token: expected expression, found Plus
```

PASSES — identical expression, continuation indented one level deeper:

```simple
fn a2(a: text) -> text:
    "x" + a
        + "y"
```

## Real-world site

`src/lib/nogc_async_mut/wm/wm_optimization.spl:55-61`:

```simple
fn dirty_rect_info(r: DirtyRect) -> text:
    "DirtyRect(sid=" + r.surface_id.to_text()
    + " x=" + r.x.to_text()
    + " y=" + r.y.to_text()
    ...
```

## Expected

A line beginning with a binary operator continues the previous expression
regardless of its indent — a line cannot start with an infix operator otherwise,
so there is no ambiguity to resolve.

## Not worked around

The source was deliberately left unchanged: reindenting it would erase the
repro and paper over a parser defect. Fix belongs in the frontend's
continuation handling.
