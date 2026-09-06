# Guide B2 — scilib ndarray: remove primitive types from public signatures

Owner: one haiku/sonnet-class agent (stdlib). Follow literally.

## Measured state (2026-09-05)

`test/03_system/plan_acceptance/scilib_port_ndarray_spec.spl` REQ-06 is RED:
`expected 5 to equal 0` — five non-underscore `fn` signatures under
`src/lib/nogc_async_mut/ndarray/` carry `f64`/`i64`/`f32`/`i32`/`u64` in a
parameter or return position. List them with exactly the spec's pattern:

```
grep -rEn '^[[:space:]]*fn [a-zA-Z][^#]*(: *| -> *)(f64|i64|f32|i32|u64)\b' src/lib/nogc_async_mut/ndarray src/lib/common/science_math/ndarray.spl
```

and the struct-field half with:

```
grep -rEn '^[[:space:]]+[a-z_][a-z0-9_]*: *(f64|i64|f32|i32|u64)[[:space:]]*$' src/lib/nogc_async_mut/ndarray src/lib/common/science_math/ndarray.spl
```

(the field count was 0 at the last run; re-check, it is asserted too).

## What to do with each hit

Decision table — no other options:

| hit is | do |
|---|---|
| an internal helper (only called from inside its own file) | rename it with a leading underscore (`fn _name`) — it was never public API |
| a public API taking/returning a primitive | change the signature to the wrapper type the plan mandates (`Float64`, `Index`, `Shape` — see `src/lib/common/science_math/ndarray.spl` for the existing wrappers) and update every caller (`grep -rn '<name>(' src test`) |

Do not add new wrapper types. Do not touch the spec.

## Acceptance

```
SIMPLE_BINARY=$PWD/src/compiler_rust/target/debug/simple \
  src/compiler_rust/target/debug/simple run test/03_system/plan_acceptance/scilib_port_ndarray_spec.spl
```

→ `7 examples, 0 failures` (REQ-07 already passes: all 16 ndarray specs run
green under `SIMPLE_BLAS_BACKEND=mock`; your renames must keep it so — the
spec re-runs them). Also `bin/simple test test/03_system/feature/scilib/`
must stay green.

Tick the two open boxes at `doc/03_plan/lib/scilib/ports/scilib_port_ndarray.md:831-832`
ONLY with `— verified <command> → 7 examples, 0 failures, <date>` appended.
