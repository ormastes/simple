# Bug: bare trailing `-1` line folds into the previous line (silent wrong value)

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** high (silent miscompute, no diagnostic)
- **Found by:** SimpleOS harden lane P7 (config_core extraction)

## Symptom
```
fn rank(x: bool) -> i64:
    if x: return 9
    -1
```
The bare `-1` is parsed as a continuation of the previous line (binary minus),
so the function returns **8** when `x` is true, and returns nil on the
fallthrough path (then core-dumps in `print`). No warning is emitted.

Block-form `if` and explicit `return -1` are unaffected.

## Impact
Any expression-position final line starting with `-` after an inline-`if`
statement silently changes the previous line's value. Worked around in
`src/lib/common/config_core/layers.spl` with explicit `return -1`.

## Next step
Lexer/parser newline handling: a leading `-` at statement position after a
complete statement must start a new expression statement, or at minimum warn.
Add regression fixture with the exact repro above. Fix in both compilers
(seed + `src/compiler/` parser).
