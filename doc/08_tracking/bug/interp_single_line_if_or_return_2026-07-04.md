# Interpreter: single-line `if A or B: return X` matches everything and swallows the function tail

- id: interp_single_line_if_or_return_2026-07-04
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- severity: high (silent wrong result — no error, wrong value returned)
- component: interpreter (single-line if-suite parsing with `or` + `return`)
- found: 2026-07-04, building the WM/GUI theme-sharing hex parser
- related: the documented "or-pattern match arm swallows early return" class
  (interp_receiver_var_and_nested_push_bugs memory / svim workarounds) — this
  is the single-line-`if` variant.

## Symptom

```
fn single_line(c: text) -> i32:
    if c == "e" or c == "E": return 14
    if c == "f" or c == "F": return 15
    -1
```

Under the gui/debug seed interpreter: `single_line("f")` returns **14**
(the FIRST or-line fires for any input reaching it), and inputs matching no
line return **nil** (the trailing `-1` is swallowed entirely). Parenthesizing
the comparisons does not help. The block form is correct:

```
    if c == "f" or c == "F":
        return 15
```

returns 15/-1 as expected.

## Repro

Probe with all three forms (single-line / block / parenthesized single-line):
`single f=14 F=14 z=nil` vs `block f=15 F=15 z=-1`.

## Impact / workaround

Any single-line `if <a> or <b>: return <x>` chain silently misdispatches —
the same shape as hand-written lookup tables (hex digits, keyword maps).
Workaround: always use block-form if-suites when the condition contains `or`
and the body is a `return`. First hit: `_wm_hex_val` in
`src/lib/common/ui/wm_chrome_theme.spl` (fixed to block form).

## Re-verification 2026-08-09 — NOT REPRODUCIBLE, marking RESOLVED

Reproduced the exact repro from this doc on the currently deployed seed
binary (`bin/release/x86_64-unknown-linux-gnu/simple`, seed-warning banner
confirmed) under both default `bin/simple run` and
`SIMPLE_EXECUTION_MODE=interpret`:

```
single_line("e") = 14   (expected 14)
single_line("E") = 14   (expected 14)
single_line("f") = 15   (expected 15, NOT 14)
single_line("F") = 15   (expected 15)
single_line("z") = -1   (expected -1, NOT nil)
```

All five cases match the documented block-form behaviour on both engines —
the originally-reported misdispatch (`single_line("f")` returning 14, or
`single_line("z")` returning nil) does not reproduce. No source change was
needed. Regression gate landed:
`test/01_unit/language/single_line_if_or_return_spec.spl` (`3 examples, 0
failures`).

**Status: RESOLVED** (verified fixed upstream, no code change required).
