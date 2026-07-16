# Pure-Simple text.split_lines method is missing at runtime

**Status:** OPEN
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

## Verification (2026-07-16)

Still reproduces at origin tip 8932fcb3a148: `probe04_split_lines_a.spl` (`content.split_lines()` on a 3-line string). Native: `native-build --entry --clean` exit 1 with `[mir-lower] WARNING: unresolved method call 'split_lines' lowered to const-0 placeholder` then `[ERROR] MIR lowering error: unresolved method call: split_lines`. No binary produced; exactly matches documented symptom.
