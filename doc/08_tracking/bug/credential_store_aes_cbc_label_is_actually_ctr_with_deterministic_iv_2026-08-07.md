# Credential store claims "AES-256-CBC" but `aes_cbc_encrypt`/`aes_cbc_decrypt` are undocumented CTR aliases, and the IV is deterministic — not random — so the mismatch is in the dangerous direction

**Date:** 2026-08-07
**Status:** OPEN — documentation only; no fix attempted this session (see
"Why no fix here" below)
**Severity:** High for the credential-at-rest encryption this actually
protects (`~/.simple/credential_key`-derived secrets stored via
`credential_encrypt`/`credential_decrypt`). Not a theoretical mislabeling —
the IV-generation code is confirmed deterministic and plaintext-derived, and
the mode actually running (CTR) is the mode most damaged by that fact.

## Summary

`src/lib/common/aes/modes.spl:86-90` (verified present, current line numbers,
on `origin/main`):

```
fn aes_cbc_encrypt(plaintext: [i64], key: [i64], iv: [i64]) -> [i64]:
    aes_ctr_encrypt(plaintext, key, iv)

fn aes_cbc_decrypt(ciphertext: [i64], key: [i64], iv: [i64]) -> [i64]:
    aes_ctr_decrypt(ciphertext, key, iv)
```

`aes_cbc_encrypt`/`aes_cbc_decrypt` are undocumented aliases for
`aes_ctr_encrypt`/`aes_ctr_decrypt` — the file has no CBC implementation at
all (no chaining, no block-chain XOR-with-previous-ciphertext, no PKCS7
padding). Nothing in `modes.spl` admits this in a comment; the module header
(lines 1-11) describes the file as pure CTR mode and never mentions CBC. The
only place "CBC" appears is in the two function names and the two `export`
lines.

**Real, security-relevant consumer:** `src/lib/nogc_sync_mut/terminal/
credential/store.spl` uses these aliases to encrypt/decrypt credentials
(passwords, API keys) at rest:

- `credential_encrypt` (line 238): `val ciphertext = aes_cbc_encrypt(pt_bytes, key, iv)`, docstring line 206: "Encrypts the plaintext using AES-256-CBC..."
- `credential_decrypt` (line 289): `val plaintext_bytes = aes_cbc_decrypt(ciphertext, key, iv)`, comment line 288: "Decrypt with AES-256-CBC"
- Module doc `src/lib/nogc_sync_mut/terminal/credential/__init__.spl:6,16`: "This module provides AES-CBC encryption..." / "Encryption: AES-256-CBC with PKCS7 padding" — there is no PKCS7 padding anywhere in this call path (CTR is a stream cipher and needs none), which is itself evidence the doc was written against an intended-but-never-built CBC path.

So every credential written through `credential_encrypt` today is encrypted
with AES-CTR while every piece of documentation at every layer (module
docstring, function docstring, inline comments, the stored-format label
users would reasonably infer) says AES-256-CBC.

## Why this is more than a naming problem: the IV is deterministic

CTR mode's security absolutely requires the (key, IV/nonce) pair to be
unique per encryption — reuse leaks `plaintext_A XOR plaintext_B` directly
from `ciphertext_A XOR ciphertext_B`, because the keystream is identical.
CBC's IV-reuse failure mode is weaker (it only leaks whether the first
plaintext blocks are equal); a real CBC implementation would have degraded
more gracefully under the same key/IV-handling code than what's actually
running.

`credential_encrypt` (`store.spl:227-235`) does not use a random or
monotonic-counter IV. It derives the IV from the plaintext itself:

```
# Generate deterministic IV from plaintext hash (for reproducibility)
# In production, use a random IV and prepend it to ciphertext
var seed: i64 = 0
val pt_bytes = text_to_bytes(plaintext)
var i = 0
while i < pt_bytes.length():
    seed = seed + pt_bytes[i] * (i + 1)
    i = i + 1
val iv = generate_iv_from_seed(seed)
```

The comment on the line above the loop already admits this is a placeholder
("In production, use a random IV..."), but it was never replaced. `seed` is
a simple weighted checksum of the plaintext bytes (no key material, no
counter, no randomness), and `generate_iv_from_seed`
(`src/lib/common/aes/utilities.spl:274-285`) expands it via a plain LCG
(`seed = seed * 1103515245 + 12345 mod 2^31`, glibc `rand()` constants) —
also fully deterministic, not cryptographically strong.

Consequences under the CTR mode that is actually running:

- **Same plaintext encrypted twice under the same key → identical
  ciphertext**, and worse, identical keystream. If the same password/token
  value is ever stored for two different credential entries (or the same
  entry is re-saved unchanged, or a value is later rotated back to a prior
  value) while using the same `~/.simple/credential_key`, the keystream
  reuse directly exposes `plaintext_A XOR plaintext_B` to anyone who can
  read the two stored ciphertexts — a much stronger primitive for an
  attacker than merely learning the two plaintexts are equal (which is all
  a real CBC implementation with the same broken IV derivation would leak).
- **The checksum is a weak, unkeyed, position-weighted sum** (`byte[i] *
  (i+1)`, summed with no modulus until it hits the LCG), so seed collisions
  between different plaintexts are far more plausible than a cryptographic
  hash would allow, further increasing the chance of accidental keystream
  reuse across genuinely different secrets.
- The credential key itself is a single long-lived file
  (`~/.simple/credential_key`, `store.spl` `credential_key_default_path`),
  reused across every credential the store ever encrypts — there is no
  per-encryption key, so IV uniqueness was the only thing that could have
  protected against keystream reuse, and it doesn't exist.

**Net effect:** the mislabel is not cosmetic. It hid the fact that the mode
actually in use (CTR) is exactly the mode that turns the pre-existing
"deterministic IV" shortcut (which the code's own comment flags as
non-production) into a direct plaintext-XOR leak, whereas the labeled mode
(CBC) would have degraded more gracefully under the identical IV bug.

## Blast radius

Any consumer relying on `credential_encrypt`/`credential_decrypt` — the
credential store's stated purpose is encrypting passwords/API keys for
on-disk config (`src/lib/nogc_sync_mut/terminal/credential/__init__.spl`
usage example: `credential_encrypt("my_secret_password", "")`). Grepped the
full tree (excluding `.claude/worktrees/*` duplicates of the same source)
for other consumers of `aes_cbc_encrypt`/`aes_cbc_decrypt` or the
"AES-256-CBC"/"AES-128-CBC" label:

- `src/lib/common/aes/modes.spl` — the alias definitions themselves.
- `src/lib/nogc_sync_mut/terminal/credential/store.spl` and `__init__.spl` —
  the only real call sites and the only "CBC" label text in production code.
- `doc/01_research/compiler/simd/cipher_simd_patterns_2026-05-02.md` —
  research doc listing `aes_cbc_encrypt`/`_decrypt` as existing CBC API
  surface (line 203) and AES ECB/CBC/CTR as supported modes (line 167);
  inherits the same mislabel but is a research doc, not a shipped claim.
- `doc/04_architecture/lib/ssh_algorithm_catalog.md` — mentions
  `aes256-cbc`/`3des-cbc`/`blowfish-cbc` as SSH cipher-suite entries marked
  "Do not implement" (SSH-CBC has its own, unrelated Lucky13 concerns) — not
  related to this module, no dependency on `aes_cbc_encrypt`.

No other production code path (config loaders, secret managers, other
credential/secret-storage modules) references these symbols or the CBC
label.

## Why this alias exists (git history)

`git log --follow` on `src/lib/common/aes/modes.spl` shows only two commits
touching this path in mainline history (`05858d83c8b`, `cfe0506e336`,
neither about AES modes specifically — this file's content is carried
through those commits, not authored by them), and `git blame` on the
CBC-alias lines shows them as uncommitted in the local working tree even
though the identical content is already present at `origin/main`
(`git cat-file -p origin/main:src/lib/common/aes/modes.spl` matches the
working file byte-for-byte) — i.e., this is not new content, it reflects
this session's local git index simply not having caught up yet, not a sign
the alias is freshly introduced. There is no comment, commit message, or
doc anywhere admitting the alias is a placeholder. The most likely
explanation, corroborated by `src/lib/common/crypto/aes_gcm.spl` exporting
only `aes128/256_encrypt_block` (forward cipher only — no AES inverse
S-box / `InvSubBytes`/`InvShiftRows`/`InvMixColumns` implementation exists
anywhere in the tree today): real CBC decryption was never implementable
without an AES decrypt-block primitive, so `aes_cbc_decrypt` was wired to
the one thing that already worked (CTR, which is its own inverse) as a
stopgap that was then never revisited, and `aes_cbc_encrypt` was aliased to
match for API symmetry. This reads as a forgotten placeholder, not a
deliberate mislabel — but the effect on anyone reading the "AES-256-CBC"
label is identical either way.

## What a correct fix requires

1. A real AES inverse-cipher block decrypt (`aes128_decrypt_block` /
   `aes256_decrypt_block`: `InvSubBytes`, `InvShiftRows`, `InvMixColumns`,
   inverse key schedule) — does not exist anywhere in the tree today
   (`src/lib/common/crypto/aes_gcm.spl` only has the forward cipher).
2. A real CBC encrypt/decrypt built on that block cipher, with PKCS7 padding
   (to match what `__init__.spl` already documents), verified against
   FIPS-197 / NIST SP 800-38A CBC known-answer-test (KAT) vectors.
3. Independently, `store.spl`'s IV derivation needs to move to a real random
   IV (or at minimum a per-encryption unique nonce, e.g. a persisted
   monotonic counter) regardless of which mode ships — the current
   deterministic, plaintext-derived IV is unsafe under either CBC or CTR,
   it is simply more dangerous under CTR.
4. Update or delete the "AES-256-CBC"/"PKCS7 padding" claims in
   `__init__.spl` and `store.spl` to match whichever mode is actually
   shipped, and add an explicit comment on any placeholder alias so this
   doesn't recur silently.

## Why no fix here (blocking dependency)

A sibling investigation this session already drafted a CBC+PKCS7
encrypt/decrypt implementation with a real AES inverse-cipher decrypt block,
and got as far as a verified AES-128 decrypt-block pass against a FIPS-197
test vector — but could not complete end-to-end verification and reverted
the draft, because of a separate, unrelated blocker: newly-added stdlib
functions are currently invisible to `bin/simple` under every execution
engine (interpreter, JIT, native), so the new decrypt-block function could
not actually be exercised by a running binary to check it against the full
NIST KAT vector set. That invisibility issue must be resolved (or a working
self-hosted binary otherwise obtained) before a real CBC fix can be verified
and landed. This doc exists to track the mislabel/exposure finding
independently of that blocker so it isn't lost.

## Unblock condition

File tracked; unblock when (a) the stdlib-function-visibility blocker is
fixed enough that a new AES decrypt-block/CBC implementation can be
exercised and verified against FIPS-197/NIST KAT vectors on a working
self-hosted `bin/simple`, and (b) `store.spl`'s IV generation is replaced
with a real random/unique-per-encryption IV.
