# Parser rejects multi-line continuation of a bare reassignment RHS (`x =\n expr`), while `val x =\n expr` is accepted

- **ID:** parser_bare_reassignment_multiline_continuation_2026-07-25
- **Status:** SOURCE FIXED / DEPLOYED ARTIFACT BLOCKED
- **Severity:** low-medium (forces a formatting workaround; asymmetric grammar)
- **Found via:** `web × headless` showcase-matrix cell — `examples/06_io/ui/web_render_file_gui.spl`
  failed to parse, blocking the web showcase's child process.

## Symptom

A declaration may continue its RHS onto the next line; a bare reassignment may not.

```
val x =
    some_expr          # OK — parses

x =
    some_expr          # FAILS — "Unexpected token: expected expression, found Newline"
```

Similarly, an unparenthesized multi-line condition fails:

```
elif a and
        b > c:         # FAILS — "Unexpected token: expected expression, found Indent"

elif (a and
        b > c):        # OK
```

## Why this is filed rather than just worked around

`.claude/rules/language.md` documents only the boolean case:

> **Multi-line booleans** — wrap in parentheses: `if (a and\n   b):` works

The reassignment case (`x =\n expr`) is **not** documented, and the
declaration-vs-reassignment asymmetry is surprising: the same RHS position
accepts a continuation after `val`/`var` but not after a bare name. Per
`CLAUDE.md`:

> When a short, safe grammar or compact expression form fails, compiles too
> slowly, or forces a workaround, fix it or record a concrete bug/feature
> request instead of silently normalizing the workaround

The occurrences in the example were normalized (see "Workaround applied"), so
this file is the required record. **The workaround is not the fix.**

## Reproduction

```
fn main() -> i64:
    var x = 1
    val y = 2
    x =
        y + 1
    x
```
Run: `<simple> run repro.spl` → `Unexpected token: expected expression, found Newline`.
Replace `x =\n y + 1` with `val z =\n y + 1` and it parses — isolating the
asymmetry to bare reassignment.

Both forms fail identically on the newly built full CLI and on the older
deployed `bin/release/x86_64-unknown-linux-gnu/simple`, so this is long-standing,
not a recent regression.

## Workaround applied (2026-07-25)

`examples/06_io/ui/web_render_file_gui.spl`: parenthesized one multi-line `elif`
condition (line ~431, matching the style already used at lines 333, 338, 342,
442, 447, 492, 536) and joined 11 two-line bare reassignments onto single lines.
12 insertions, 22 deletions, no functional change. The file now parses.

## Source fix and remaining artifact work

Commit `ab63c351d142` now suppresses layout after all assignment tokens, and
`dedent_continuation_spec.spl` covers bare, field, compound, and walrus
continuation through the current parser source. The deployed Stage2 and old
Stage3 binaries predate that source fix. A current-source Stage3 build produced
no progress for the bounded three-minute attempt, so target binaries remain
blocked until a fresh pure-Simple compiler artifact is admitted.

**2026-07-31 clarification:** `ab63c351d142` is pure-Simple-self-hosted-only
(`src/compiler/10.frontend/core/*.spl`); it never touched
`src/compiler_rust/parser`. The Rust seed parser had the same symptom as an
independent defect, fixed in
`doc/08_tracking/bug/seed_assignment_trailing_equals_continuation_2026-07-31.md`.
