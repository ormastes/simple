# `text.to_int()` optional is a lie + `Some(<i64>)` payload shifted x8 on JIT

- **Filed:** 2026-07-27 (lane TOINT)
- **Status:** OPEN — compiler/runtime defects, NOT patched here (parallel lanes
  are live in both compiler trees). Library call sites fixed defensively.
- **Severity:** BUG-1 (security-relevant fail-open) + BUG-2 (silent data corruption)

## BUG-1 — `.to_int()` is typed `i64?` but can never return nil

`text.to_int()` type-checks as an optional (`x ?? d` and `x == nil` both
compile against it), but the runtime backing it returns a plain integer:

```c
/* src/runtime/runtime_native.c:2889 */
int64_t rt_string_to_int(int64_t value) {
    ...
    return (int64_t)strtoll(buf, NULL, 10);   /* 0 on failure; nil unrepresentable */
}
```

So every invalid input arrives as the integer `0`, indistinguishable from a
legitimate `"0"`. Guards of the shape

```
val parsed = value.to_int()
if parsed == nil: return nil        # <-- DEAD CODE, never taken
```

are fail-OPEN. Where 0 is a meaningful value (session id, row id, port, index,
CRC) this is a security defect: lane DBTIER found `session=notanumber` being
admitted as session 0 in the DB server.

### Repro — `build/toint_probe/probe_to_int.spl`

`bin/simple run` (bootstrap-seed binary, `bin/release/x86_64-unknown-linux-gnu/simple`),
identical under `SIMPLE_EXECUTION_MODE=interpreter`:

| input | `== nil` | `?? -999` | expected |
|---|---|---|---|
| `""` | false | 0 | nil |
| `"0"` | false | 0 | 0 (ok) |
| `"abc"` | false | 0 | nil |
| `"12abc"` | false | 0 | nil |
| `"abc12"` | false | 0 | nil |
| `" 12"` | false | 12 | 12 (ok) |
| `"+12"` | false | 12 | 12 (ok) |
| `"-12"` | false | -12 | -12 (ok) |
| `"0x1f"` | false | 0 | nil |
| `"99999999999999999999999"` | false | 0 | nil |
| `"1_000"` | false | 0 | nil |

`?? default` NEVER fires for any input. Note the C runtime is a *lenient*
strtoll prefix parse while the Rust seed is a strict whole-string parse, so
`"12abc"` is `12` natively and `0` on the seed — an additional engine
divergence.

### Fix options
1. Change `rt_string_to_int`'s lowering to a genuinely optional return
   (nil for a failed parse). Preferred; it makes the declared type true.
2. If (1) breaks callers, re-declare `.to_int()` as `-> i64` (total, 0 on
   failure) so it stops lying, and route optional callers to the new
   `std.convert.try_parse_int`.

## BUG-2 — `Some(n)` where `n: i64` returns `8 * n` on the JIT backend

Isolated, minimal, engine-divergent. Repro `build/toint_probe/probe_some.spl`:

```
fn via_some(n: i64) -> i64?:  Some(n)
fn via_bare(n: i64) -> i64?:  n
```

| n | `Some(n) ?? -1` (JIT) | `Some(n) ?? -1` (interp) | bare (both) |
|---|---|---|---|
| 0 | 0 | 0 | 0 |
| 1 | **8** | 1 | 1 |
| 12 | **96** | 12 | 12 |
| 100 | **800** | 100 | 100 |
| 4242 | **33936** | 4242 | 4242 |

Tag-box shift (`<<3`) applied on construction and not undone on unwrap.
`src/lib/nogc_sync_mut/database/core.spl` `get_i32`/`get_i64` returned
`Some(parsed)`, so **every integer column read out of an SDN row was 8x too
large under the JIT.**

**Workaround (applied):** return the bare value from an `i64?` function; never
wrap an i64 in an explicit `Some(...)`.

## BUG-3 (related) — i64 magnitude ceiling is 2^60-1 under the JIT

`build/toint_probe/probe_optmax.spl`: on the JIT an i64 literal/value above
`2^60-1` is already truncated (`9223372036854775807` reads back as `-1`,
`2^61` as `0`); the interpreter is exact. `std.convert.try_parse_int` therefore
refuses magnitudes above `1152921504606846975` rather than returning a mangled
number.

## BUG-4 (related) — `.?` is a zero-test, not a presence test, on i64 optionals

`build/toint_probe/probe_opt.spl`: for `val r: i64? = 0`, `r.?` is **false**
on the JIT (and evaluates to the payload `0`, not a bool, on the interpreter),
while `r == nil` correctly reports false. Any presence check written with `.?`
silently rejects a valid `Some(0)`. All fixed call sites use `== nil`.

## BUG-5 (minor, pre-existing) — COLL006 false positive on integer accumulators

`bin/simple lint src/lib/common/convert.spl` reports
`error[COLL006]: string concat in loop (O(n^2))` for `result = result * 10 + d`
inside a `while`, where `result` is an i64. Reproduces at HEAD on
`safe_parse_int` (`git show HEAD:src/lib/common/convert.spl` → 1 COLL006), so
it is not introduced by this lane's change. The linter is classifying an
integer accumulator as a string concatenation.

## Library-side mitigation landed by this lane

- `src/lib/common/convert.spl` — new fail-closed `is_int_text`,
  `try_parse_int`, `try_parse_in_range`, `try_parse_i32/u16/u32/u64`;
  fail-open siblings re-documented as such.
- `src/lib/nogc_sync_mut/database/core.spl` — `get_i32`/`get_i64` and the
  `#sdn-crc32:` header check.
- `src/lib/nogc_sync_mut/database/wal.spl` — WAL line CRC check.
- `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/http_server/utilities.spl`
  — `Range:` header.
- `src/lib/nogc_sync_mut/redis/client.spl` — RESP bulk length / array count.
- `src/lib/{nogc_sync_mut,nogc_async_mut}/database/feature_utils.spl` — `to_int_or`.
- Spec: `test/01_unit/lib/common/convert_fail_closed_spec.spl`.
