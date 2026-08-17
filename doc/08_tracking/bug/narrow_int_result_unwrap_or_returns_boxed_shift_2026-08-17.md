# `Result<u8>.unwrap_or` returns 222<<3; `(u8?)` via `!` returns the nil tag

Status: OPEN (P1)
**Found:** 2026-08-17 — interpreter, `bin/simple run` probe (no daemon involved)

## Symptom

Narrow integer payloads lose their boxing shift on the way out of an Option /
Result accessor. Exit 0, no diagnostic, plausible-looking integer:

| expression | expected | actual |
|---|---|---|
| `Result<u8>.unwrap_or(...)` | `222` | **`1776`** |
| same shape at `Result<i64>` | correct | correct |
| `(u8?)` unwrapped via `!` | `222` | **`3`** |

`1776 == 222 << 3`. Tag 0 is a boxed int stored as `v << 3`, so the value is
being handed back still boxed — the shift is never undone on this path. `3` is
the nil tag word, i.e. the second case reads an untagged/absent slot.

This is width-specific: the identical construction at `i64` is correct, so it is
not the generic Option machinery. It is the narrow-int (`u8`) transport.

## Why this is the silent class

Both results compile clean and exit 0. `1776` and `3` are perfectly plausible
integers; nothing distinguishes them from a real answer at the call site.

## Not the ByteBuffer defect it was found under

Isolated *away* from `ByteBuffer`, which is innocent — `to_bytes`, `push_u8` and
`get` all return `222,173` correctly. The original row's framing was wrong.

## Related family

Same low-3-bit tag family as the JIT defects fixed 2026-08-17 (raw-slot branch,
omitted-field nil placeholder), but this one is INTERPRETER-side and narrow-int
specific, so those fixes do not cover it.

## Not proven
Root cause file:line not located. Only `u8` was exercised; `u16`/`u32`/`i8`
untested. Native/AOT lanes untested.
