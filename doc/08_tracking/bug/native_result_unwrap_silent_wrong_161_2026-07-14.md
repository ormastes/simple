# native-build: `.unwrap()`/`.unwrap_or()` on `Result` silently returns 161

**Severity:** high (silent-wrong — violates the never-loud→silent discipline)
**Found:** 2026-07-14, errhandling lane
**Resolved:** 2026-07-15
**Backend:** native-build `--entry` (pure-Simple MIR lowering)

## Symptom

Calling `.unwrap()` or `.unwrap_or(d)` on a `Result<T,E>` value returns a fixed
wrong constant (`161`) for **both** `Ok` and `Err` — never panics, never emits a
diagnostic, never matches the payload.

```simple
fn f() -> Result<i64, text>: return Ok(7)
fn main() -> i64:
    print(f().unwrap())   # native prints 161; oracle prints 7
    return 0
```

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` L156-260:
`.unwrap`/`.unwrap_or` branch **exclusively** on `rt_is_some`/`rt_is_none`, which
is the **Option** runtime representation. There is no case for `Result`'s
`rt_enum_new`/`rt_enum_discriminant` representation, so the payload extraction
reads the wrong slot and yields a constant.

## Resolution

MIR now recovers a receiver's declared `Result<Ok,Err>` type through the same
typed-expression/symbol/call-return helper used by Result match lowering. A
shared Result-only unwrap path branches on `rt_enum_discriminant`, extracts the
raw Ok payload through `rt_enum_payload`, lazily evaluates the `unwrap_or`
default for Err, and calls `rt_panic` for `Err.unwrap()`.

The existing Option implementation remains unchanged. The first safe scope is
`i64` and `text` Ok payloads; other Result payload shapes fail compilation with
`unsupported Result unwrap payload type` instead of being silently coerced.

`scripts/check/check-native-seed-parity.shs` covers numeric/text `unwrap`, both
`unwrap_or` branches, unchanged numeric Option behavior, an unsupported
`u64` loud failure, and a required runtime panic diagnostic in the 43-case
gate. The Result case is native-authoritative because the seed oracle's
`Result.unwrap_or` behavior is itself broken.

## Reproduce

`/tmp/wt_errhandling/p*.spl` (errhandling lane probes). Oracle:
`env -u SIMPLE_BOOTSTRAP bin/simple run p.spl`; native:
`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean`.
