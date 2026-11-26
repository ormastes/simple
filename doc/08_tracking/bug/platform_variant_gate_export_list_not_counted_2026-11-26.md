# Platform variant gate does not count names exposed through `export` lists

Date: 2026-11-26
Status: open
Component: `scripts/check/check-platform-variant-dirs.shs`

## Problem

The `api:` check compares public names across sibling platform variants. Its
regex now counts only `pub fn` / `pub extern fn` / `extern fn` names. A bare
`fn x` made public through an `export x` list (a legal Simple pattern, used for
example in `io/file_ops.spl`) is not counted, so a variant that drops or never
had such a name is not reported: a public-API gap through export lists is missed.

## Expected fix

- Also collect names listed in `export a, b, c` statements (and the alias target
  of `export use ... as name`) into the per-variant name set (`NM` / `ALLN`).
- Add a `--selftest` fixture: a sibling variant exposing `fn x` via `export x`
  while another variant lacks it must report one `api` offender; the same name
  present in both must report none.
- Keep the baseline count at 207 unless the new rule finds real existing gaps;
  record any newly found gaps in the baseline deliberately, not silently.
