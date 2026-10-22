# Seed JIT: unwrapping a `u64?` returns a pointer-like value

Date: 2026-10-18. Found by: independent review of the BLAKE3/XXH3/gzip lane.
Binary: Rust seed `bin/local/seed_simple` (sha256 prefix 9c45d2bf601ab93e), default JIT.
Interpreter mode is correct. Self-hosted compiler not checked (no pure-Simple CLI on
this aarch64 host).

## Symptom
For `fn maybe(ok: bool) -> u64?` returning `0xea224fb077ddcacd`:

| form | JIT | interpreter |
|---|---|---|
| `val a: u64 = r ?? 0u64` | correct | correct |
| `val b: u64 = r.unwrap()` | `hi=938 lo=402733985` (pointer-like) | correct |
| `val c = maybe(true) ?? 0u64` | `hi=938 lo=402734001` | correct |

Repro: `test/fixtures/compiler/seed_jit_optional_u64_unwrap_repro/main.spl`
(`SIMPLE_EXECUTION_MODE=jit` vs `interpreter`).

## Impact / workaround
`xxh3_64_with_secret` was briefly `-> u64?`; it now returns `[u64]` (`[]` on a rejected
secret, `[hash]` otherwise), matching `xxh3_128_with_secret`, which is correct in both
modes. Avoid `u64?` return types in hot library APIs until this is fixed; if one is
unavoidable, unwrap only with `val x: u64 = opt ?? default`.
Related: `seed_jit_untyped_to_u8_push_double_untag_2026-10-18.md` (same family: a boxed
value read without a static type is not untagged).

## Status
OPEN in the seed JIT (src/compiler_rust). Library side avoids the shape.
