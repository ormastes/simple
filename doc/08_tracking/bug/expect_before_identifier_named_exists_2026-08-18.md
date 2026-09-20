# `expect <ident>` fails when the identifier is named `exists` (2026-08-18)
## Obsolete 2026-09-16 — referenced path(s) gone, e.g. test/{02_,}integration/lib/std/screenshot/screenshot_ffi_spe

Reviewed in the 2026-09-16 bug-ledger normalization pass. Kept for history;
the subject is removed, superseded, or duplicated elsewhere in the ledger.

## Status
OPEN — seed parser/desugar defect, found while fixing the screenshot SFFI externs.

## Symptom
```
val exists = false
expect exists == false     # semantic: variable `expect` not found
```
Renaming the local (`present`) makes the identical assertion pass, so the value
and the comparison are fine; the parse of `expect` followed by an identifier
named `exists` is what breaks — `expect` ends up parsed as a variable reference.

## Reproduce (minimal, 2 examples: 1 fails, 1 is the positive control)
```
describe "expect with a local named exists":
    it "accepts a local named exists":
        val exists = false
        expect exists == false
    it "accepts the same value under another name":
        val present = false
        expect present == false
```
Observed: `Results: 2 total, 1 passed, 1 failed`.

## Impact
Blocks the last example of
`test/{02_,}integration/lib/std/screenshot/screenshot_ffi_spec.spl`
("checks if screenshot exists"). The spec is deliberately left unchanged —
renaming the local would hide the defect.

## Next step
Find where `exists` is treated as a keyword/postfix operator in the seed parser
and stop it from swallowing the `expect` statement head.

