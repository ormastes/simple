# `src/lib/common/aes/` scalar AES is non-functional: `expand_key` produces a wrong schedule from word 4 on, and `aes_encrypt_block`/`aes_decrypt_block` fail FIPS-197 C.1 — while the only specs covering them are round-trip-only and pass anyway

**Date:** 2026-08-08
**Status:** OPEN
**Severity:** Medium. No production crypto path consumes these (enumerated
below), but they are exported stdlib functions with the obvious names, they
are wrong, and the four specs covering them are structurally incapable of
noticing.

> **CORRECTION NOTICE (read first).** An earlier revision of this doc, landed
> in commit `e51dcaaf8ba`, quoted the failing output as
> `a038909860609818008018a060a880f8` and
> `004080c0004080c0004080c0004080c0`, and speculated about "transposed state
> indexing" from the shape of those bytes. **Those constants were wrong** —
> they came from a hex-formatting helper in the probe script that was itself
> miscompiling (see
> `doc/08_tracking/bug/list_param_helper_functions_miscompile_2026-08-08.md`).
> The commit message of `e51dcaaf8ba` repeats them and cannot be rewritten;
> this doc is the correction of record. The *conclusion* — that this AES is
> broken — survives re-measurement and is if anything stronger, but every
> number below has been re-taken by comparing raw `list` values directly, with
> no formatting helper anywhere in the path.

## Finding (clean measurement)

Found while implementing real AES-CBC for the credential store
(`credential_store_aes_cbc_label_is_actually_ctr_with_deterministic_iv_2026-08-07.md`).
`cipher.spl` was evaluated for reuse and rejected because it fails FIPS-197
Appendix C.1.

Probe via `bin/simple run`, printing raw lists (no hex helper), FIPS-197 C.1
key `000102030405060708090a0b0c0d0e0f`, plaintext
`00112233445566778899aabbccddeeff`:

```
get_round_key(expand_key(key,16), 0)
  got  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  want [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]     CORRECT

get_round_key(expand_key(key,16), 1)
  got  [64, 72, 16, 24, 32, 104, 176, 248, 64, 8, 208, 152, 96, 40, 240, 184]
  want [214, 170, 116, 253, 210, 175, 114, 250, 218, 166, 120, 241, 214, 171, 118, 254]
                                                                  WRONG

aes_encrypt_block(pt, key)
  got  [148, 39, 82, 19, 12, 204, 211, 227, 192, 240, 3, 180, 44, 149, 112, 95]
  want [105, 196, 224, 216, 106, 123, 4, 48, 216, 205, 183, 128, 112, 180, 197, 90]
                                                        (= 69c4e0d8...) WRONG

aes_decrypt_block(ct, key)
  got  [128, 136, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232, 240, 248]
  want [0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255]
                                                                  WRONG
```

## Root cause locus: `expand_key`'s word-derivation loop

The clean data localises this precisely, and it is *not* where the retracted
revision guessed:

- **Round key 0 is correct.** `expand_key`'s first loop (`expanded.append(key[i])`
  for `i < key_size`, `key_expansion.spl:55-58`) copies the key verbatim, and
  `get_round_key(exp, 0)` returns exactly the input key. So both the copy loop
  and `get_round_key`'s indexing are fine.
- **Round key 1 is already wrong**, i.e. the very first *derived* word. The
  defect is therefore in `expand_key`'s word loop (`key_expansion.spl:52+`)
  and/or the helpers it calls — `get_key_word`, `rotate_word`, `xor_words`,
  `rcon_lookup`, `sub_bytes`.
- Everything downstream (`aes_encrypt_block` through the SIMD facade,
  `aes_decrypt_block` through the scalar path) is fed a garbage schedule, so
  both being wrong is fully explained by this one defect. There is no need to
  hypothesise a second bug in the round functions — though they have not been
  independently verified either, since they cannot be until the schedule is
  correct.

Note also a structural oddity worth fixing regardless:
`aes_encrypt_block` routes through `_simd_aes_encrypt_block_with_expanded`
(the `std.simd_crypto` facade) while `aes_decrypt_block` routes through
`_scalar_aes_decrypt_block_with_expanded`. Encrypt and decrypt therefore run
entirely different implementations, which is precisely why a round-trip test
gives so little assurance here.

**Caveat on mechanism:** it has not been established whether `expand_key` is
wrong *as source* or is being miscompiled by the engine. A verbatim local copy
of `pkcs7_unpad` from the same directory family reproduces that function's
misbehaviour identically (see the companion doc), so an engine-level cause for
this cluster cannot be ruled out and should be checked before rewriting the
source. Whoever fixes this must determine which it is first.

## Why the existing tests do not catch it

Every spec that exercises these functions asserts only that
`decrypt(encrypt(x)) == x`. That passes under any bug symmetric between the
forward and inverse paths — and a shared garbage key schedule is exactly such
a bug, since both directions consume the same wrong schedule. None compares
against a published vector:

- `test/01_unit/lib/common/simd_dispatch_facade_spec.spl` (and its
  `test/unit/...` duplicate) — `@cover src/lib/common/aes/cipher.spl`,
  round-trip only.
- `test/03_system/core/variant_api_parity_spec.spl` (and its `test/system/...`
  duplicate) — round-trip only.

Any fix must land a KAT assertion, not another round trip.

## Consumers (enumerated, not assumed)

`grep -rn "aes_encrypt_block\|aes_decrypt_block\|std.common.aes.cipher"`,
excluding vendored code and `.claude/worktrees` duplicates:

- `examples/02_language_features/cipher/aes_minimal.spl` — round-trips
  successfully while producing non-AES ciphertext.
- The four specs above.
- `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` and the
  `test/*/compiler/mir_opt/cipher/*` specs reference the module path only as
  **string symbol names** (`"std.common.aes.cipher.aes_round_software"`) for
  MIR pattern matching; they never call the functions. Unaffected by the
  numeric defect — but if the round functions are renamed during a fix, those
  strings must be updated in lockstep.

No production encryption path calls `cipher.spl`. `src/os/crypto/aes_xts.spl`
and `src/os/crypto/ocb3.spl` use `rt_aes_decrypt_block_with_expanded` and
their own `_aes_decrypt_block_pure`; different implementations, not implicated.

## Relationship to the CBC fix

`src/lib/common/aes/modes.spl` CBC does **not** use this code, and deliberately
so. It builds on `src/lib/common/crypto/aes_gcm.spl`, whose forward cipher and
new inverse cipher both pass FIPS-197 C.1 **and** C.3 exactly, in both
directions, under KAT assertions that compare raw lists.

This means the tree currently holds two AES inverse ciphers. That duplication
is real and is a known hazard, but consolidating onto this one is not
currently possible: it is broken, and `modes.spl`'s CBC *encrypt* half is on
`aes_gcm.spl`'s schedule layout, so routing only the decrypt half here would
straddle CBC across two implementations with incompatible schedules — strictly
worse than the duplication. Consolidation becomes possible once this defect is
fixed and KAT-gated, at which point CTR and GCM would have to move too.

## What a fix requires

1. Add FIPS-197 C.1/C.2/C.3 KAT assertions (both directions) plus an
   `expand_key` schedule assertion against the published round keys, to
   `simd_dispatch_facade_spec.spl`. This goes in FIRST and must be seen to
   fail.
2. Determine source-vs-engine (see the caveat above) before editing.
3. Fix `expand_key`'s word loop, then re-verify the round functions
   independently now that the schedule is trustworthy.
4. Only then consider consolidating the two AES implementations.

## Verified on

Interpreter only, via `bin/simple run`, which on this box is the Rust bootstrap
seed (prints the "bootstrap seed only" banner). Not checked on JIT, native, or
a self-hosted binary.
