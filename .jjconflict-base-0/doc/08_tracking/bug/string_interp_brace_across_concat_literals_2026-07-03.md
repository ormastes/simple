# String interpolation brace scanner breaks across concatenated string literals

- **Date:** 2026-07-03
- **Severity:** P1 (wrong runtime string content — silent source-text leak)
- **Found by:** dashboard HTML/CSS generation in examples/12_business/simple_erp/src/web/dashboard.spl

## Repro

When a string literal opens a `{` brace whose matching `}` lands in a
*different* concatenated literal, the interpolation scanner mis-tracks the
brace depth and leaks raw source text (including the following line's code)
into the runtime string:

```
var css = "body{font:14px;"
css = css + "color:#1a1f26;}"
# runtime value of css contains literal source text from the next line
```

## Expected

`{` inside a string literal either starts an interpolation that must close in
the SAME literal, or (if unmatched) should be a parse error — never silent
leakage of adjacent source lines into the string value.

## Workaround

Keep `{`/`}` balanced within each single literal (e.g. one CSS rule per
literal). Applied in dashboard.spl.
