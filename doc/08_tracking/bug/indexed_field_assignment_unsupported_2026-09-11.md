# Assignment to a field of an indexed element is rejected: "complex indexed field receiver is not supported"

**Filed:** 2026-09-11 · **Status:** open · **Area:** compiler / semantics
**Binary:** `bin/release/aarch64-apple-darwin-macho/simple`, size 26264696, mtime 1788766698

## Symptom

A short, obvious mutation of one element's field inside an array is refused:

```simple
var receipt = base()          # receipt.rows: [ChromeShowcaseTabRow]
receipt.rows[3].nonblank = false
```

```
semantic: invalid assignment: complex indexed field receiver is not supported
```

Reading the same path (`receipt.rows[3].nonblank`) works. Only assignment through an
indexed element's field is refused.

## Why this is a defect and not a style preference

`.claude/rules/code-style.md` and CLAUDE.md both require that a short, safe form which
fails be fixed or filed rather than silently normalised into a workaround. The workaround
is three extra statements and a full struct reconstruction per mutation:

```simple
var rows = receipt.rows
rows[3] = ChromeShowcaseTabRow(tab: "t3", wall_ms: 12, pixels: 57600,
    nonblank: false, ppm_path: "build/chrome-showcase/t.ppm")
receipt.rows = rows
```

That restates every field, so it silently loses any field the author forgets — exactly the
class of error the direct form cannot make. In a test fixture (where this was hit) it also
makes the *intent* of the fixture harder to read: "this one tab is blank" becomes a
five-line rebuild.

## Reproduction

`test/01_unit/app/ui/chrome_web_showcase_receipt_spec.spl`, the example
"fails when any tab produced a blank frame or no PPM". The direct form is preserved in a
comment there, pointing at this record; reverting the comment to live code reproduces the
error immediately (1 of 17 examples fails).

## Scope not yet established

Not investigated here: whether the same refusal covers `arr[i].f += x`, nested indexing
(`a[i].b[j].c = v`), dict-element field assignment, or whether it differs between the
interpreter and native codegen. The failure above was observed on the interpreter path
(`SIMPLE_EXECUTION_MODE=interpreter`) only.

## Resume

Locate the `complex indexed field receiver is not supported` message in the assignment
lowering path and determine whether the restriction is a lowering gap or a deliberate
aliasing guard. If deliberate, the message should say so and name the supported form.
