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

## Re-verification attempt 2026-08-17 — NOT REPRODUCED as filed; STILL OPEN

Binary identity: `readlink -f bin/simple` ->
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`;
`stat -c '%s %y'` -> `59537240 2026-08-17 12:58:51.339525019 +0000`.

The record carries **no minimal repro** (only a symptom table and an explicit
"Root cause file:line not located"), so two reconstructions of the described
shapes were built. Neither reproduces `1776` or `3` on either engine:

`r4.spl` — `fn okv() -> Result<u8, string>: return Ok(222u8)`,
`fn optv() -> u8?: return 222u8`, plus the `i64` control:

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run r4.spl
res_u8_unwrap_or: 222
res_i64_unwrap_or: 222
opt_u8_bang: 222
$ SIMPLE_EXECUTION_MODE=jit bin/simple run r4.spl
res_u8_unwrap_or: 222
res_i64_unwrap_or: 222
opt_u8_bang: 222
```

`r4b.spl` — `u8` sourced from a `[u8]` array (`Result<u8,string>` wrapper,
`xs.get(0)!`, `xs.first().unwrap_or(0u8)`):

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run r4b.spl
arr_res: 222
arr_opt_bang: 222
arr_first: 222
$ SIMPLE_EXECUTION_MODE=jit bin/simple run r4b.spl
arr_res: 222
arr_opt_bang: 222
arr_first: <value:0xde>     <- NEW, different defect (see below)
```

Status therefore stays **OPEN**, but for a changed reason: the filed
interpreter-side `1776` / `3` symptom did not reproduce in any reconstruction,
and the record does not pin down the shape that produced it. It is not closed as
fixed, because "my reconstruction differs from theirs" is not evidence of a fix.
**Next step for whoever owns this: supply the exact original program** (the
ByteBuffer-adjacent probe it was isolated from), or close it as unreproducible.

### Adjacent finding, JIT-only, NOT the filed defect
`xs.first().unwrap_or(0u8)` on `var xs: [u8] = [222u8, 173u8]` prints
`<value:0xde>` under `SIMPLE_EXECUTION_MODE=jit` and `222` under the
interpreter — a `u8`-typed value escaping unrendered rather than mis-shifted.
Same optional-accessor family as
`coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17.md`; recorded
here only because it was found by this reconstruction, not asserted as the same
bug.

**Not fixed here** either way: every candidate site is in the Rust bootstrap
seed, so it is out of scope for a pure-Simple fix, and the record's root cause
is still unlocated — deliberately not guessed at.
