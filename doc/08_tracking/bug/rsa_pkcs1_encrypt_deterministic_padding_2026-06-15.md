# rsa_pkcs1 type-2 padding used fixed 0xFF PS

Status: RESOLVED (2026-10-19)

`_pkcs1_v15_pad_type2` in `src/lib/common/crypto/rsa_pkcs1.spl` filled PS with
0xFF, violating RFC 8017 7.2.1 (PS must be >= 8 random nonzero octets):
deterministic ciphertext, Bleichenbacher-style structure fully predictable.

## Fix
PS is now drawn from the OS CSPRNG via `csprng_bytes`
(`std.common.aes.utilities`, backed by `rt_random_i64` in both the interpreter
and native runtime) with zero bytes rejection-sampled. Malformed entropy
(wrong length / out-of-range byte) returns `[]`, so `rsa_pkcs1_public_encrypt`
returns `[]` - never a fixed fill. No new direct `rt_*` call.

`entropy_platform_bytes` (`rt_entropy_fill`) was the preferred owner but that
extern has no runtime backing in the seed (every call is `Err`), so it was not
usable; switch to it once `rt_entropy_fill` is backed.

## Evidence
`test/01_unit/lib/crypto/rsa_pkcs1_padding_spec.spl` (e=1, all-0xFF modulus
exposes the padded block). Base: passed=1 failed=2 (both engines). Fix:
passed=3 failed=0 (jit and interpreter). Sabotage (constant PS) -> failed=1.
`check-no-direct-rt --roots src`: forbidden 5980 base and tip.
