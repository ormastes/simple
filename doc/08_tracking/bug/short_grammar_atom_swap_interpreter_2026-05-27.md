## Closed 2026-09-13 — JIT divergence issue, tracked separately

Date: 2026-05-27
Status: STALE 2026-05-29 — coordination_native_spec passes with placeholder grammar as-is

> Re-checked 2026-09-13 (Windows x86_64, seed `bin/simple` v1.0.0-rc.1): this closure stands for the INTERPRETER path — `["ready"].map("{_1}:migrated")` returns `ready:migrated` when the function is demoted to the interpreter. It does NOT hold under the Cranelift JIT, where every `text`-returning inline lambda yields a raw handle integer. Not reopened; the JIT divergence is tracked separately in `jit_inline_lambda_text_return_raw_handle_2026-09-13.md`.

---

# Short Grammar Placeholder Fails For Atom Swap In Interpreter

## Summary

`Atom.swap` and `Atom.swap_returning_old` from `std.nogc_async_immut` accept
explicit callback lambdas in interpreter mode:

```spl
atom.swap(\x: x + 4)
atom.swap_returning_old(\x: x * 2)
```

Changing those callbacks to placeholder short grammar makes the interpreter
run of `test/01_unit/lib/nogc_async_immut/coordination_native_spec.spl` fail one
example:

```spl
atom.swap(_1 + 4)
atom.swap_returning_old(_1 * 2)
```

## Evidence

The same spec passes with explicit atom callbacks while other callbacks in the
file, such as `Ref.new(4, _1 >= 0)`, `ref.swap_validated(_1 + 1)`, and
`cas_loop(atomic, _1 + 1, 3)`, pass in interpreter mode.

Native mode accepted the broader placeholder migration during probing. The gap
appears specific to interpreter execution of atom swap callback placeholders.

## Impact

Keep atom swap callbacks explicit in interpreter-covered coordination tests
until the interpreter supports placeholder short grammar for these callbacks.

