# Pure-Simple text.split_lines method is missing at runtime

**Status:** source fixed; interpreter and strict dual-backend execution pending
**Severity:** High for self-hosted compiler/tooling paths
**Affected surface:** compiled pure-Simple method dispatch for `text`

## Symptom

The deployed pure-Simple CLI exits during `native-build --entry-closure` with:

```text
Runtime error: Function 'str.split_lines' not found
```

Requirements and comparison documents list `text.split_lines()` as built in,
but the self-hosted runtime method table does not expose that method.

## Current containment

`_native_build_entry_closure` uses `content.split("\n")`, which is supported
and retains the required linear-time scan. This is not evidence that
`split_lines()` itself works.

## Completion criteria

- Register one canonical `text.split_lines()` implementation for interpreter
  and compiled pure-Simple execution.
- Define CRLF and trailing-empty-line behavior and match it in both modes.
- Add interpreter and native execution tests that call the method directly.
- Remove this bug only after a deployed Stage 4 binary passes those tests.

## Verification (2026-07-17)

Pure-Simple interpreter dispatch and MIR lowering now accept both
`split_lines()` and its canonical `lines()` alias. Empty input returns `[]`;
CRLF normalization, trailing-newline suppression, repeated trailing LF, and
lone CR match Rust `str::lines()`. The strict dual-backend parity case covers
both names and those edge cases. Execution remains pending in the staged full
gate; do not mark the deployment criterion complete until that gate runs.
