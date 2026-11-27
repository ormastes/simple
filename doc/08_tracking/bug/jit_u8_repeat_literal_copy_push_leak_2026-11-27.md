# Seed JIT: [0u8; n] copy-then-push leaks more than a push-built [u8] (2026-11-27)

Status: open, P3. Seed: /home/yoon/.cache/cargo-target-wr-seed1126b/release/simple, SIMPLE_EXECUTION_MODE=jit.

## Repro
In `_pbkdf2_cat_u8(a, b)` (`var r: [u8] = a` then `r.push(b[i])`), pass `a` as a 64-byte pad built
with `[0u8; 64]` plus index stores. Run PBKDF2-HMAC-SHA256 for 20000 iterations: RSS is 172 MB. Build
the same pad with `push` instead and RSS is 131-137 MB. With 1 iteration both shapes use 94 MB.
Digests are identical.

## Workaround
`_pbkdf2_u8_pad` in `src/lib/common/crypto/pbkdf2.spl` builds the pad with push
(`@workaround(jit_u8_repeat_literal_copy_push_leak_2026-11-27)`).
