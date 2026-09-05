# Lane TOINT — `to_int()` fail-open numeric parsing

Date: 2026-07-27. Status: work complete, NOT committed (lane is no-commit).

## Verdict

`text.to_int()` is typed `i64?` but **can never return nil**. The runtime
behind it (`rt_string_to_int`, src/runtime/runtime_native.c:2889) returns a
plain `int64_t`, 0 on failure. Every `if parsed == nil` / `?? default` guard
written against it is dead code, so garbage is admitted as the integer 0 —
indistinguishable from a legitimate "0". Lane DBTIER's `session=notanumber`
→ session 0 is the concrete exploit.

## Truth table — `.to_int()`

Binary: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple` (prints
the bootstrap-seed banner). **Identical under the default engine and
`SIMPLE_EXECUTION_MODE=interpreter`.** Probe: `build/toint_probe/probe_to_int.spl`.

| input | `== nil` | `?? -999` | correct |
|---|---|---|---|
| `""` | false | 0 | nil |
| `"0"` | false | 0 | 0 |
| `"abc"` | false | 0 | nil |
| `"12abc"` | false | 0 | nil |
| `"abc12"` | false | 0 | nil |
| `" 12"` | false | 12 | 12 |
| `"+12"` | false | 12 | 12 |
| `"-12"` | false | -12 | -12 |
| `"0x1f"` | false | 0 | nil |
| `"99999999999999999999999"` | false | 0 | nil |
| `"1_000"` | false | 0 | nil |

`?? default` never fires. The C runtime is a lenient strtoll prefix parse
while the Rust seed is a strict whole-string parse, so `"12abc"` is 12
natively and 0 on the seed — an extra engine divergence.

## Contract chosen

`.to_int()` is a compiler/runtime intrinsic and lanes are live in both
compiler trees, so it was NOT patched (step-5 rule). Instead:

1. **Added a fail-closed sibling** in `src/lib/common/convert.spl`:
   `is_int_text`, `try_parse_int -> i64?`, `try_parse_in_range`,
   `try_parse_i32/u16/u32/u64`. `try_parse_int` genuinely returns nil, and
   `"0"` is a real value distinct from failure.
2. **Corrected the lenient functions' docs** so they stop lying:
   `safe_parse_int` / `parse_u16` / `parse_u32` / `parse_u64` are now labelled
   FAIL-OPEN with a pointer to the try_* siblings.
3. Filed the intrinsic defect as a bug doc.

## Three further defects found (all filed, none patched in the compiler)

- **`Some(<i64>)` returns 8x the value on the JIT** (tag-box shift). 12 -> 96,
  100 -> 800. Interpreter is correct; a bare return is correct on both.
  `database/core.spl` `get_i32`/`get_i64` used `Some(parsed)`, so every
  integer DB column was **8x too large under the JIT**.
  Repro `build/toint_probe/probe_some.spl`.
- **i64 magnitude ceiling is 2^60-1 under the JIT** — `9223372036854775807`
  reads back as `-1`. `try_parse_int` therefore refuses above `2^60-1`.
  Repro `build/toint_probe/probe_optmax.spl`.
- **`.?` on an i64 optional is a zero-test, not a presence test** — false for
  a valid `Some(0)` on the JIT; on the interpreter it evaluates to the payload
  rather than a bool. All fixed sites use `== nil`.
  Repro `build/toint_probe/probe_opt.spl`.

## Caller sweep

- 288 `.to_int()` sites in owned `src/**` (vendor excluded).
- 77 in off-limits trees (compiler, compiler_rust, ui, ecs, llm,
  browser_engine/security, database/server).
- **211 in scope**; 45 of those carry a dead non-zero `?? default` guard.
- **15 fail-open hazards fixed** (untrusted input or integrity checks).
- Remainder classified benign: CLI-arg / UI-layout / editor fallbacks where 0
  or the default is harmless.

### Hazards fixed
| file | what |
|---|---|
| `src/lib/nogc_sync_mut/database/core.spl` | `get_i32`, `get_i64` (+ dropped `Some(i64)`), `#sdn-crc32:` header check |
| `src/lib/nogc_sync_mut/database/wal.spl` | WAL line CRC trailer |
| `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/http_server/utilities.spl` | `Range:` header start+end (6 sites) |
| `src/lib/nogc_sync_mut/redis/client.spl` | RESP bulk length, array count |
| `src/lib/nogc_sync_mut/stomp/subscribe.spl` | `content-length` header |
| `src/lib/{nogc_sync_mut,nogc_async_mut}/database/feature_utils.spl` | `to_int_or` overflow fallback |

### Known remaining (not fixed, lower priority / other lanes)
- `src/app/ui.web/server.spl:712` — port `?? 8080` dead, garbage → port 0.
- `src/lib/common/ui/**`, `src/compiler/**` — off-limits to this lane.

## Verification

All spec verdicts below come from **`bin/simple run <spec>`**, which executes
the sspec and prints the per-describe `N examples, M failures` lines.

> **Runner caveat — `bin/simple test` NEVER produced a verdict.**
> `bin/simple test test/01_unit/lib/common/convert_fail_closed_spec.spl` was
> run twice, both times with a definitive non-result:
>   1. **Exited 0** after printing only unrelated lint warnings from
>      `test_runner_types.spl` — **zero examples, no `N examples, M failures`
>      line at all.** A silent false-green: exit 0 with nothing executed.
>   2. Re-run against the final spec: **killed at the 900 s timeout with a
>      0-byte output file** — no verdict, no examples, no progress.
>
> Do NOT read an exit-0 from `bin/simple test` on this spec as a pass. This
> looks like the same family as the already-filed
> `doc/08_tracking/bug/test_level_filters_never_match_numbered_trees_2026-07-27.md`
> (another lane). The `bin/simple run` verdicts below are the load-bearing
> ones, and they are the only executed evidence in this lane.

- `test/01_unit/lib/common/convert_fail_closed_spec.spl` — **14 examples, 0 failures** (`bin/simple run`).
- Deliberate red: changed `try_parse_int`'s `return nil` to `return 0` (the
  fail-open regression) → **14 examples, 6 failures**, including
  "must not admit a non-numeric session id as session 0". Reverted, green again.
- No regression: `convert_spec.spl` 22/0, `convert_parsing_spec.spl` 22/0.
- Lint parity vs `git show HEAD:<file>` on every modified file — error counts
  unchanged. Pre-existing and NOT introduced here:
  - `convert.spl` COLL006 "string concat in loop" is a false positive on an
    integer accumulator (present at HEAD on `safe_parse_int`); the new
    functions share the shape.
  - `database/core.spl` "method `get` not found on type `str`" fails at HEAD
    too, so `SdnRow` could not be executed standalone — the `get_i32`/`get_i64`
    fix is source-level + lint-parity verified, **not runtime-verified**.

## Artifacts
- `src/lib/common/convert.spl`
- `src/lib/nogc_sync_mut/database/{core,wal,feature_utils}.spl`
- `src/lib/nogc_async_mut/database/feature_utils.spl`
- `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/http_server/utilities.spl`
- `src/lib/nogc_sync_mut/redis/client.spl`, `src/lib/nogc_sync_mut/stomp/subscribe.spl`
- `test/01_unit/lib/common/convert_fail_closed_spec.spl`
- `doc/08_tracking/bug/to_int_optional_lies_and_some_i64_payload_shift_2026-07-27.md`
- `build/toint_probe/probe_{to_int,opt,some,optmax,tryparse,sdnrow}.spl`

## Note to the coordinator
`src/lib/common/convert.spl` was **silently reverted mid-session** by a
parallel sync while I was editing it (the Edit tool reported "file has been
modified"). Re-verify the file content before landing.
