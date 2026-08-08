# `src/lib/common/aes/cipher.spl` `aes_encrypt_block`/`aes_decrypt_block` produce wrong AES, and their only tests are round-trip-only so they pass anyway

**Date:** 2026-08-08
**Status:** OPEN
**Severity:** Medium. No production crypto path is known to consume these
(enumerated below), but they are exported stdlib functions named exactly what
a caller would reach for, they are wrong, and the three specs covering them
are structurally incapable of noticing.

## Finding

Found while implementing real AES-CBC for the credential store
(`credential_store_aes_cbc_label_is_actually_ctr_with_deterministic_iv_2026-08-07.md`).
`cipher.spl` was evaluated for reuse and rejected because it fails the
FIPS-197 Appendix C.1 known-answer test outright.

Probe (interpreter, `bin/simple run`), FIPS-197 C.1:

```
plaintext  00112233445566778899aabbccddeeff
key        000102030405060708090a0b0c0d0e0f

aes_encrypt_block  -> a038909860609818008018a060a880f8   WRONG
expected           -> 69c4e0d86a7b0430d8cdb78070b4c55a

aes_decrypt_block("69c4e0d8...", key) -> 004080c0004080c0004080c0004080c0   WRONG
expected                              -> 00112233445566778899aabbccddeeff
```

The output is not noise — the byte pattern `00 40 80 c0` repeating four times
is highly structured, suggesting the column/row indexing of the `list`-based
state (`state_get`/`state_set`, `shift_rows`, `mix_columns`) is transposed or
the SIMD dispatch facade (`simd_aes_round` / `simd_aes_round_last` from
`std.simd_crypto`) is being fed a differently-ordered state than the scalar
path assumes.

For contrast, the independent typed (`[u8]`) implementation in
`src/lib/common/crypto/aes_gcm.spl` passes C.1 **and** C.3 exactly, in both
directions, under the same probe harness. So the defect is specific to
`cipher.spl`, not to the runtime or the probe.

## Why the existing tests do not catch it

Every spec that exercises these functions asserts only that
`decrypt(encrypt(x)) == x`. A round trip passes under ANY bug that is
symmetric between the forward and inverse paths — which is exactly what a
consistently-transposed state index produces. None of them compares against a
published vector:

- `test/01_unit/lib/common/simd_dispatch_facade_spec.spl` (and its
  `test/unit/...` duplicate) — `@cover src/lib/common/aes/cipher.spl`,
  round-trip only, for both `aes_*_block` and `aes_*_block_with_expanded`.
- `test/03_system/core/variant_api_parity_spec.spl` (and its `test/system/...`
  duplicate) — round-trip only.

This is the spec-vacuity pattern: a green suite that cannot fail for the thing
it appears to be testing. Any fix must land a KAT assertion, not another round
trip.

## Consumers (enumerated, not assumed)

`grep -rn "aes_encrypt_block\|aes_decrypt_block\|std.common.aes.cipher"` over
the tree (excluding vendored code and `.claude/worktrees` duplicates):

- `examples/02_language_features/cipher/aes_minimal.spl` — a language-feature
  example that encrypts and decrypts a block. It "works" (round-trips) while
  producing non-AES ciphertext, so it demonstrates the API with wrong output.
- The four specs listed above.
- `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` and the
  `test/*/compiler/mir_opt/cipher/*` specs reference the module path only as
  **string symbol names** (`"std.common.aes.cipher.aes_round_software"`) for
  MIR pattern matching. They never call the functions, so they are unaffected
  by the numeric defect — but note that if the round functions are renamed
  during a fix, those symbol strings must be updated in lockstep.

No production encryption path (credential store, TLS, SSH, OS crypto) calls
`cipher.spl`. `src/os/crypto/aes_xts.spl` and `src/os/crypto/ocb3.spl` use
`rt_aes_decrypt_block_with_expanded` / their own `_aes_decrypt_block_pure`,
which are different implementations and are not implicated here.

## What a fix requires

1. Add FIPS-197 C.1/C.2/C.3 KAT assertions (both directions) to
   `simd_dispatch_facade_spec.spl` — this must go in FIRST and be seen to
   fail, or the fix is unverified.
2. Root-cause the state ordering. Compare `state_get`/`state_set` indexing and
   `shift_rows`/`mix_columns` against `aes_gcm.spl`'s verified column-major
   (`index = 4*column + row`) convention, and check whether the SIMD facade
   path (`_simd_aes_encrypt_block_with_expanded`) and the scalar path
   (`_scalar_aes_decrypt_block_with_expanded`) agree on that convention —
   note that encrypt goes through the SIMD facade while decrypt is
   scalar-only, which is where an ordering mismatch would hide.
3. Alternatively: delete `cipher.spl`'s block API and reroute the example and
   specs to the verified `aes_gcm.spl` functions. But note the repo rule that
   deleting a reimplementation REROUTES rather than dedupes — the `list`-typed
   API surface differs from the `[u8]` one, so this is not a drop-in.

## Verified on

Interpreter only, via `bin/simple run` (which on this box is the Rust
bootstrap seed and prints the "bootstrap seed only" banner). Not checked on
JIT, native, or a self-hosted binary — but note the failure is a wrong
*constant*, not an engine divergence, so it is unlikely to be engine-specific.
