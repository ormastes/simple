# Bug: `grid` unusable as a local variable name — parser keyword collision

## Closed 2026-09-13 — fixed, re-verified by running the entry repro

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

Ran the exact repro from the "Repro" section:

```spl
fn f() -> text: "x"
fn main() -> i64:
    val grid = f()
    print(grid)
    0
```

Result: parses and runs, prints `x`, exit 0. The `expected Colon, found RParen`
parse error no longer occurs — `grid` is accepted as an ordinary local name.
The "focused execution pending" caveat in the Resolution section is now
discharged (measured, not inferred).

**Date:** 2026-07-03
**Severity:** medium (misleading diagnostics)
**Status:** source fixed in Rust parser 2026-07-15; focused execution pending — CLOSED 2026-09-13 (see top section)

## Symptom
`val grid = some_call(x)` fails to parse with `Unexpected token: expected
Colon, found RParen` — the parser treats `grid` as the UI-layout contextual
keyword and expects `grid:`. The error location/message gives no hint the
identifier is the problem.

## Repro
```
fn f() -> text: "x"
fn main() -> i64:
    val grid = f()   # parse error: expected Colon, found RParen
    0
```
Renaming `grid` to any other identifier fixes it.

## Expected
Contextual keywords should only be recognized in their layout context, or the
diagnostic should say the identifier collides with a keyword.

## Resolution

`grid` remains a lexer token for the literal grammar, but expression dispatch
now selects that grammar only before `:` or `device`. Otherwise the token is an
ordinary identifier. Declaration patterns already accepted it, and the
pure-Simple lexer already treated it contextually. Focused execution is pending.
