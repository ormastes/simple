# `if val x = <Result expr>` binds the whole Result instead of the Ok payload

Status: OPEN. Severity: P2. Found 2026-11-07 (lane m-result).

## Observed
`module_surfaces_from_modules` changed from `Option<ModuleSurfacesByName>` to
`Result<ModuleSurfacesByName, text>`. Specs that still wrote
`if val surfaces = module_surfaces_from_modules(...)` kept compiling; the binder
received the whole `Result`, so the first field access failed at runtime with
`semantic: undefined field: unknown property or method 'ordered_names' on Result`
(interpreter, `bin/simple.exe` 2026-11-04). Hit in
`test/01_unit/compiler/result_err_record_owner_spec.spl` (14/15 red) and
`test/01_unit/compiler/mir/result_try_provider_tuple_spec.spl` (10/10 red).

## Expected
`if val` on a non-Optional `Result` should be a compile error (or a defined
Ok-unwrap), never a silent bind of the carrier.

## Repro
```
fn r() -> Result<i64, text>: Ok(1)
fn main():
    if val x = r():
        print(x + 1)   # binds Result, not 1
```

## Workaround applied (callers only)
Both specs now `match ... case Ok(surfaces) / case Err(reason)`. The language
gap itself is not fixed here.
