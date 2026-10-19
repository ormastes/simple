# PBKDF2-HMAC-SHA-384/512 has no runtime fast path

- Date: 2026-10-19
- Status: open (primitive landed 2026-10-20; default switch waits on binary redeploy)
- Spec: test/01_unit/lib/common/crypto/pbkdf2_native_perf_spec.spl (SHA-384 c=4096, SHA-512 c=80000) stays red; not skipped.
- Cause: the only runtime hash extern was `rt_tls13_sha256` (SHA-256). No SHA-384/512 or HMAC extern existed, so these variants run pure Simple in the interpreter (~9.5 ms per HMAC; 160k HMACs for c=80000 cannot fit the 900 s budget).
- Done: PBKDF2-HMAC-SHA-256 uses a fast path over `rt_tls13_sha256` (`pbkdf2_sha256_fast_spec`).
- Done 2026-10-20: runtime primitive `rt_sha512_digest` / `rt_sha384_digest` in the C runtime, the Rust runtime and the interpreter registry (typed wrappers `std.nogc_sync_mut.sffi.host.sha512_digest` / `sha384_digest`), plus opt-in `pbkdf2_sha384_bytes_fast` / `pbkdf2_sha512_bytes_fast` in `src/lib/common/crypto/pbkdf2.spl`. Specs: `sha512_runtime_primitive_spec`, `pbkdf2_sha512_fast_spec`. With the public names switched to the fast path, the perf spec measured 9/9 in 12.6 s on a lane-built seed.
- Why the default is not switched yet: `src/lib` is read as source on every run, and a binary that does not register the extern fails hard (`unknown extern function: rt_sha512_digest`); it does not return an empty digest, so the length-check fallback cannot fire. No extern-availability probe exists. Switching now would turn bip39, SCRAM-SHA-512, `pbkdf2_industry_vectors_spec` and `crypto_reference_spec` red on every binary built before the change.
- Remaining: after the seed and the pure-Simple binary are redeployed on every deployed triple, make `pbkdf2_sha384_bytes` / `pbkdf2_sha512_bytes` call `_pbkdf2_sha2_512_family_bytes(..., 48 / 64)` (the `_fast` bodies), and keep the current bodies as `_pure` for the fast-vs-pure specs.
- Found on the way: `test/01_unit/os/crypto/bip39_kat_spec.spl` fails TV2 (the computed seed diverges from the expected one after byte 30; check which matches the published BIP-39 vector) and calls undefined `_tv4_seed` / `_tv5_seed` / `_tv6_seed`. This was hidden before because the pure path timed out at 900 s.
