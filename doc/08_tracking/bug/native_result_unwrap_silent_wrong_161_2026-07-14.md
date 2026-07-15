# native-build: `.unwrap()`/`.unwrap_or()` on `Result` silently returns 161

**Severity:** high (silent-wrong — violates the never-loud→silent discipline)
**Found:** 2026-07-14, errhandling lane
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

## Fix direction

Dispatch on `receiver.type_` (populated by MIR-lowering time — the same pattern
the method already uses to read the receiver): when the receiver is a `Result`,
extract via `rt_enum_discriminant`/`rt_enum_payload` (Ok = variant 0 payload);
`.unwrap()` on `Err` should **loud-fail** (build-time is fine, or a runtime
panic), never return a constant. `.is_ok()/.is_err()` are already correctly
loud-unsupported and can be wired at the same time.

## Reproduce

`/tmp/wt_errhandling/p*.spl` (errhandling lane probes). Oracle:
`env -u SIMPLE_BOOTSTRAP bin/simple run p.spl`; native:
`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out --clean`.
