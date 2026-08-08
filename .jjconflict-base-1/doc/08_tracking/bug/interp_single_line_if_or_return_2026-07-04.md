# Interpreter: single-line `if A or B: return X` matches everything and swallows the function tail

- id: interp_single_line_if_or_return_2026-07-04
- status: open
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
