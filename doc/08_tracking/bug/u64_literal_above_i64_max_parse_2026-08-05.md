# A `u64` literal above `i64::MAX` fails to parse

**Filed:** 2026-08-05
**Area:** compiler / frontend / lexer-parser, lint
**Severity:** low (workaround exists) — but silent-ish: the diagnostic names
the whole file, not the literal.

## Symptom

A `u64` literal whose value exceeds `i64::MAX` (9223372036854775807) does not
parse. The whole file is then dropped by the linter:

```
error[PARSE001]: NOT LINTED: source did not parse - every AST-based lint was
skipped for this file
```

No message points at the literal, so the failure reads as "this file is
broken" rather than "this token is unsupported", and every other lint for the
file is silently skipped.

## Reproduction

```simple
val huge: u64 = 18446744073709551360u64   # 2^64 - 256
fn f() -> u64: huge
```

`bin/simple lint <file>` → `Found 1 error(s) ... NOT LINTED`.

The same file with a value at or below `i64::MAX` lints clean, and the
arithmetic form of the same value lints clean and evaluates correctly:

```simple
val huge: u64 = 0u64 - 256u64    # lints clean; prints 18446744073709551360
```

## Why it matters

`u64` exists precisely to express the top half of the 64-bit range — pointer
sentinels, address-space limits, mask constants. Requiring authors to write
them as wrapping subtractions hides the intent of the constant.

Found while writing `test/01_unit/os/kernel/ipc/ipc_wire_transfer_spec.spl`,
which needs a near-`u64`-max pointer to exercise the IPC user-pointer
wraparound guard. The spec currently carries the `0u64 - 256u64` workaround
with a comment pointing here.

## Expected

Either the literal parses, or the diagnostic names the offending token and
its position instead of failing the entire file with a file-level PARSE001.
