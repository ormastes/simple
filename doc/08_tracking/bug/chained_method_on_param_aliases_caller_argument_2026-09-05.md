# Chained method call on a function PARAMETER aliases and clobbers the caller's argument

- **Filed-on:** 2026-09-05
- **Area:** compiler / interpreter (Rust seed, `src/compiler_rust/target/debug/simple`)
- **Priority:** P1
- **Status:** open

## Symptom

`axpy(2.0, a, b)` returned the right answer *and silently overwrote the
caller's `a`*. `test/03_system/plan_acceptance/scilib_port_blas_spec.spl`
(REQ-SCILIB-BLAS-11) caught it: `dot(a, b)` immediately after the `axpy` call
read **47.0** instead of 11.0, because `a` had become `[5, 8]` — `dot([5,8],[3,4])
= 15 + 32 = 47`.

## Minimal reproduction

```
fn f1(alpha: Float64, x: NDArray, y: NDArray) -> NDArray:
    x.mul_scalar(alpha).add(y)          # chained on the parameter

fn f2(alpha: Float64, x: NDArray, y: NDArray) -> NDArray:
    val t = x.mul_scalar(alpha)         # intermediate bound to a local
    t.add(y)

fn f3(alpha: Float64, x: NDArray, y: NDArray) -> Result<NDArray, LinalgError>:
    Ok(x.mul_scalar(alpha).add(y))      # chained inside Ok(...)
```

With `a = [1,2]`, `b = [3,4]`, alpha = 2:

| call | result | caller's `a` afterwards |
|------|--------|--------------------------|
| `f1` | `[5,8]` | **`[5,8]` — CLOBBERED** |
| `f2` | `[5,8]` | `[1,2]` — correct |
| `f3` | `[5,8]` | **`[5,8]` — CLOBBERED** |

The same chain written against a *local* `val` (not a parameter) is pure:
`val m = a.mul_scalar(2.0)` leaves `a` at `[1,2]` and `m.add(b)` leaves `m` at
`[2,4]`. Both `mul_scalar` and `add` are individually non-mutating. Only the
chained form applied to a parameter aliases.

## Impact

Every Layer C routine written in the natural chained style silently mutates its
caller's arrays. This is a correctness hazard well beyond linalg: it is not a
wrong number, it is action at a distance in the caller's data.

## Workaround in force

`src/lib/nogc_async_mut/linalg/mod.spl` (`try_axpy`) binds the scaled
intermediate to a local before `.add(y)`, with a comment pointing here. Remove
the workaround when this defect is fixed — a `TODO(scilib)` marks the site.

## Verification lane

`src/compiler_rust/target/debug/simple run <spec>` (debug Rust seed built from
current source). Not reproduced against a deployed pure-Simple binary — none is
deployed on this host.
