# Seed JIT: erased ints (list.get / tuple element) reach typed i64 params without unboxing

## Status: ALREADY FIXED in seed source (verified 2026-11-06)

Fixed by `6581807d48c fix(seed): untag erased T values bound to scalar call parameters`
(2026-10-31): `coerce_args_for_param_slots`
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs:327`) now UNBOXES a
tagged (`Any`/`T?`) argument bound to a raw scalar parameter, for direct and method
calls. The binaries that showed this (`bin/simple.exe` 0b2c3d015b7, and the 2026-10-05
`src/compiler_rust/target/bootstrap/simple.exe`) predate that commit.

Evidence, `test/fixtures/compiler/seed_jit_miscompiles/erased_int_typed_call.spl`
(`[Any]` element, `[Any]` sum, untyped-list `.get`, tuple destructure into `modq(x: i64)`),
`SIMPLE_EXECUTION_MODE=jit`:
- 2026-10-05 seed: `any=1342 sum=2725 list=2725 tup=2725` (x8, as recorded);
- seed built from `origin/release/1.0.0` @ 475d1983381: `any=1000 sum=1589 list=1589 tup=1589`
  (= interpreter).
Regression test: `compiler/tests/erased_scalar_boundary_jit.rs`
`erased_ints_reach_typed_i64_params_untagged` (passes on 475d1983381 without further
change). The `.spl` workarounds in `ml_kem_ntt.spl` / `ml_kem_kpke.spl` are no longer
needed by the seed but were not reverted here. The `_absorb_block` private-name clash
mentioned below is a separate symbol-resolution issue and was not re-checked.

## Open 2026-11-04 — seed-side root cause, worked around in .spl

Found while fixing `x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05`.
Under `SIMPLE_EXECUTION_MODE=jit` (bin/simple.exe, release 0b2c3d015b7) an
untyped local initialised from `list.get(i)` or from a destructured tuple
element, once used in arithmetic and passed to a function with an `i64`
parameter, reaches the callee still tagged (value << 3): `modq(fj + t)` with
`fj + t == 1589` returned `12712 % 3329 == 2725`. The interpreter is correct.
Declaring the local `val x: i64 = ...` (or `val n: i64 = tuple_elem`) makes the
JIT unbox it. Other fallout of the same class: `var n = n_in` style loops,
`_absorb_block` private-name clash between `lib.common.crypto.sha3` ([i64]) and
`os.crypto.ml_kem_kpke` (list) resolved to the wrong co-compiled body.

Repro: `SIMPLE_EXECUTION_MODE=jit bin/simple.exe run` of any program calling
`fn modq(x: i64) -> i64` with `list.get(a) + list.get(b)`; compare with
`SIMPLE_EXECUTION_MODE=interpreter`. Pre-fix hybrid KEM gave non-deterministic
JIT output (secret != recovered).

Worked around (not fixed) in `src/os/crypto/ml_kem_ntt.spl` and
`ml_kem_kpke.spl` with typed locals. The seed should coerce erased values at
typed call boundaries; sibling `.spl` code with the same shape is unaudited.
