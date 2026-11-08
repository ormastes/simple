# `as <int>` on an optional returned from a function silently evaluates to 0

- **id:** optional_as_cast_yields_zero_2026_11_09
- **status:** OPEN
- **severity:** P2 — silent wrong value; masked a spec red for two months
- **found:** 2026-11-09, diagnosing `acpi_spec_three_reads_return_zero_2026-09-19`

## Symptom

```simple
fn mk(v: u64) -> u64?:
    if v != 0:
        v
    else:
        nil

val r = mk(0xFED00000)
expect(r ?? 0).to_equal(0xFED00000)   # passes
expect(r as u64).to_equal(0xFED00000) # FAILS: expected 0 to equal 4275044352
```

A locally-typed optional does NOT reproduce (`val r: u32? = 0xB008; r as u32`
equals `0xB008`), so the defect is specific to an optional produced by a
function return (boxed `Some`). Measured on the Windows Rust seed
`bin/simple.exe`, release/1.0.0 @ e954b1d95e2, interpreter lane.

## Expected

Per the nil-only-in-unsafe policy (memory `nil-only-in-unsafe`, ERR-01), `T?`
must be narrowed with `??` or a nil check before use as `T`; `T? as T` outside
`unsafe` should be a compile error. Silently yielding 0 is the worst outcome:
it satisfied every `to_be_nil` assertion and turned real payloads into zeros.

## Where to look

Interpreter `as` cast evaluation on an `Option`/boxed value (cast of a non-int
Value to int falls through to 0) and the type checker's cast admissibility rule
for optional sources. Prevention: make the cast a type error; add a spec that a
`T?` function return cast with `as` is rejected.

## Related

- `acpi_spec_three_reads_return_zero_2026-09-19.md` — the symptom this hid.
