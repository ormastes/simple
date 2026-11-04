# Seed JIT: erased ints (list.get / tuple element) reach typed i64 params without unboxing

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
