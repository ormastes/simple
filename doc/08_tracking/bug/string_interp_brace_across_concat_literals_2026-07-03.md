# String interpolation brace scanner breaks across concatenated string literals

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
