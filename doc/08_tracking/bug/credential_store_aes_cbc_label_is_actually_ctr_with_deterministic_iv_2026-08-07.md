# Credential store claims "AES-256-CBC" but `aes_cbc_encrypt`/`aes_cbc_decrypt` are undocumented CTR aliases, and the IV is deterministic — not random — so the mismatch is in the dangerous direction

**Date:** 2026-08-07
**Status:** FIXED 2026-08-08 — real CBC + PKCS#7 implemented, OS-CSPRNG IV,
versioned on-disk format with a legacy read path. See "Resolution" at the
bottom. (The "Why no fix here" section below records the state as of
2026-08-07 and its stated blocker, which did NOT reproduce.)
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

## Resolution (2026-08-08)

Fixed. Four parts:

### 1. Real AES inverse cipher (FIPS 197 §5.3 / Figure 12)

Added to `src/lib/common/crypto/aes_gcm.spl` — the typed (`[u8]`) AES that
`modes.spl` already builds CTR and GCM on:
`_aes_gcm_aes_inv_sbox_table`, `_aes_inv_sbox`, `_aes_inv_sub_bytes`,
`_aes_inv_shift_rows`, `_aes_inv_mix_columns`, `_aes_decrypt_block`, and the
exported `aes128_decrypt_block` / `aes256_decrypt_block`. It consumes the
SAME forward round schedule from `aes128_key_expansion` /
`aes256_key_expansion`, in reverse round order.

**Correction to this doc's original premise:** an inverse cipher *did* already
exist elsewhere — `src/lib/common/aes/cipher.spl` has
`aes_decrypt_block`/`inv_mix_columns`/`inv_shift_rows`, and
`src/lib/common/aes/sbox.spl` has `aes_inv_sbox`. It was not reused because it
is **broken**: probed against FIPS-197 C.1 its *forward* `aes_encrypt_block`
returns `a038909860609818008018a060a880f8` instead of
`69c4e0d86a7b0430d8cdb78070b4c55a`, and its decrypt is correspondingly wrong.
That is a separate defect, now filed with an enumerated consumer list as
`doc/08_tracking/bug/aes_cipher_spl_block_functions_fail_fips197_c1_2026-08-08.md`.
Enumerated (not assumed): its only callers are
`examples/02_language_features/cipher/aes_minimal.spl` and four specs
(`simd_dispatch_facade_spec.spl`, `variant_api_parity_spec.spl`, and their
`test/unit`/`test/system` duplicates) — all of which assert ONLY
`decrypt(encrypt(x)) == x`, which passes under any symmetric bug, so the
suite is structurally incapable of catching it. No production crypto path
calls it.

### 2. Genuine CBC in `src/lib/common/aes/modes.spl`

`aes_cbc_encrypt`/`aes_cbc_decrypt` no longer alias the CTR functions. They do
real chaining plus PKCS#7 (`_pkcs7_pad_16`/`_pkcs7_unpad_16`, local to the
module). `aes_ctr_encrypt`/`aes_ctr_decrypt` are untouched and still exported.

Two deliberate behaviour changes callers must know about:

- **Length is no longer preserved.** CBC output is the plaintext length
  rounded up to the next multiple of 16, and a block-aligned plaintext still
  gains a whole padding block. `store.spl` was the only caller in the tree.
- **`aes_cbc_decrypt` now returns `[i64]?` and fails CLOSED** — `nil` on a bad
  key size, bad IV size, non-block-multiple ciphertext, or invalid PKCS#7
  padding. This is deliberately *unlike* the pre-existing
  `std.common.aes.padding.pkcs7_unpad`, which returns its input unchanged when
  validation fails and would therefore hand raw padding bytes back as
  "plaintext" under a wrong key.

The IV stays a caller-supplied parameter: `src/lib/common/**` is the pure tier
and has no OS randomness, and a parameterised IV is what makes the NIST
fixed-IV vectors testable.

### 3. IV source and on-disk format migration in `store.spl`

- IV now comes from `rt_random_hex(16)`, which is backed by the OS CSPRNG
  (`rand::rngs::OsRng`, see `src/compiler_rust/compiler/src/interpreter_extern/
  random.rs`). It is declared `-> text?` and `credential_encrypt` returns `""`
  if the OS refuses — it never falls back to a predictable IV. The same
  primitive is already used by `src/lib/nogc_sync_mut/security/types.spl`.
  (Note: `rt_random_hex` is registered in the seed interpreter's extern table
  and in `runtime_symbol_entries.rs`; no hand-written C implementation was
  found under `src/runtime/`.)
- **Format is now versioned:** `encrypted:v2:<hex_iv><hex_ciphertext>`.
  Detection is unambiguous because a v1 payload is pure lowercase hex and
  neither `v` nor `:` is a hex character, so neither version can be
  misclassified as the other.
- **Existing credential files are NOT corrupted.** `credential_decrypt`
  branches on the marker *before* any layout-dependent slicing; a v1 record
  takes an explicit, commented read-only path that calls `aes_ctr_decrypt` by
  name, because those bytes really are CTR bytes. Records are not silently
  re-encrypted on read; re-saving a credential upgrades it to v2. Users need
  to do nothing.
- Docstrings/labels in `store.spl` and `__init__.spl` now describe what the
  code actually does, including the v1/v2 split.

### 4. Verification

New regression specs:

- `test/01_unit/lib/crypto/aes_cbc_fips197_nist_spec.spl` — 18 specs, all
  green: FIPS-197 C.1 (AES-128) and C.3 (AES-256) block KATs in **both**
  directions; NIST SP 800-38A F.2.1 (AES-128-CBC) and F.2.5 (AES-256-CBC)
  chaining vectors compared against the leading 64 bytes of the padded output;
  a guard that CBC output differs from CTR output in both length and content;
  PKCS#7 round-trips at 0/1/15/16/17/40/100 bytes; and fail-closed nil returns
  for wrong key, unaligned ciphertext, empty ciphertext, and bad IV size.
- `test/01_unit/lib/terminal/credential_store_cbc_migration_spec.spl` — v2
  marker, round-trip, **two encryptions of the same plaintext differ** (the
  security crux), and a real v1 CTR record still decrypting.

RED→GREEN→SABOTAGE was performed: flipping one byte of the new inverse S-box
(`0xd5` → `0xd6` at index 3) turned 7 of the 18 specs red, including the C.3
AES-256 decrypt KAT, proving the published-vector assertions can actually
fail. The file was restored and re-verified by blob hash.

**Engine verified: interpreter only**, via `bin/simple test`, which on this box
is the Rust bootstrap seed (it prints the "bootstrap seed only" banner). JIT,
native, and a self-hosted `bin/simple` were **not** exercised. Given the known
native/JIT divergences recorded for dict and list operations, the CBC path
should be re-verified on the self-hosted binary when one is available.

### 5. The blocker cited in "Why no fix here" did not reproduce

Newly-added stdlib functions were immediately visible. `aes128_decrypt_block`
and `aes256_decrypt_block` were added to `aes_gcm.spl` and called successfully
from a scratch script on the first attempt, returning correct FIPS-197 values.
Consistent with
`doc/08_tracking/bug/new_stdlib_fn_not_found_could_not_reproduce_2026-08-07.md`.

---

# Claim audit — 2026-08-08

Independent re-verification of every factual claim above, measured against
`origin/main` blobs (`git cat-file -p origin/main:<path>`), not the shared
working copy. Verdicts:

| # | Claim | Verdict | Evidence |
|---|-------|---------|----------|
| 1 | `aes_cbc_encrypt`/`aes_cbc_decrypt` are bare aliases for the CTR functions; no CBC, no chaining, no padding in `modes.spl` | **TRUE** | `origin/main:src/lib/common/aes/modes.spl:86-90` verbatim as quoted. Only CBC text in the file is the two `fn` names + two `export` lines. |
| 2 | `store.spl` labels the output "AES-256-CBC" while calling those aliases; `__init__.spl` claims PKCS7 padding that this call path does not perform | **TRUE** | `origin/main` `store.spl` docstring "Encrypts the plaintext using AES-256-CBC", comment "# Encrypt with AES-256-CBC" at the `aes_cbc_encrypt` call, and `use std.common.aes.modes.{aes_cbc_encrypt, aes_cbc_decrypt}` at line 15. No padding call anywhere in the path. |
| 3 | The IV is derived deterministically **from the plaintext** | **TRUE** | `credential_encrypt` computes `seed = Σ pt_bytes[i]*(i+1)` over `text_to_bytes(plaintext)` and passes it to `generate_iv_from_seed`, which is a bare glibc LCG (`utilities.spl`: `current_seed = (current_seed*1103515245 + 12345) % 2147483648`). No key material, no counter, no randomness, no time input anywhere on the path. Traced end to end. |
| 4 | The key is long-lived and shared across every credential | **TRUE** | Single `~/.simple/credential_key` via `credential_load_key`; no per-encryption key derivation. So (key, IV) uniqueness rests entirely on the IV, which is a pure function of the plaintext ⇒ same plaintext ⇒ same keystream ⇒ `ct_A ^ ct_B = pt_A ^ pt_B`. The CTR-vs-CBC analysis in this doc is correct. |
| 5 | "No AES inverse cipher (`InvSubBytes`/`InvShiftRows`/`InvMixColumns`) exists anywhere in the tree today" | **FALSE** | A complete pure-Simple AES inverse cipher has been on `origin/main` all along, in the **same directory as `modes.spl`**: `src/lib/common/aes/sbox.spl:80 inv_sub_bytes` (+ inverse S-box table), `src/lib/common/aes/cipher.spl:57 inv_shift_rows`, `:172 inv_mix_column`, `:213 inv_mix_columns`, `:346 aes_inv_round_software`, `:391 _scalar_aes_decrypt_block_with_expanded`, `:428 aes_decrypt_block`, `:447 aes_decrypt_block_with_expanded`. There is also a native `rt_aes_decrypt_block_with_expanded` in the Rust runtime (`src/compiler_rust/runtime/src/value/aes.rs:469`) with its own round-trip test, and the compiler's MIR-opt pattern rules already reference `std.common.aes.cipher.aes_inv_round_software` by fully-qualified symbol (`src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl:39`). The original investigation checked only `src/lib/common/crypto/aes_gcm.spl` and did not check the sibling files in `src/lib/common/aes/`. |
| 5a | Corollary — "real CBC decryption was never implementable without an AES decrypt-block primitive" (the doc's stated root cause for the alias) | **FALSE** | Follows from #5. The primitive existed. The alias is an unexplained shortcut, not a forced one. |
| 5b | Corollary — "What a correct fix requires, item 1: [an AES inverse cipher] does not exist anywhere in the tree today" | **FALSE** | Same evidence. Item 1 of the fix plan was already done. Likewise PKCS#7: `src/lib/common/aes/padding.spl` has had `pkcs7_pad`/`pkcs7_unpad` on `origin/main` all along — though note `pkcs7_unpad` **fails open** (returns its input unchanged on invalid padding), which is a separate latent defect and means it should not be used as-is for CBC. |
| 6 | Could an `export` list have hidden the inverse cipher, making it "exist but be unreachable"? | **NO — `export` is not a visibility gate** | `src/lib/common/aes/utilities.spl` contains **zero** `export` lines, yet `store.spl:16` successfully imports six symbols from it (`generate_iv_from_seed` among them) on the live path this bug is about. Top-level `fn`s in a file with no export list are importable. `cipher.spl`/`sbox.spl` are in exactly that shape, so their inverse-cipher functions are importable today. |
| 7 | Blast radius: `nogc_sync_mut` is the only implementation and only "CBC" label in production code | **TRUE, but slightly understated** | The implementation is indeed only `src/lib/nogc_sync_mut/terminal/credential/store.spl` (11,078 bytes); the `gc_async_mut` / `gc_sync_mut` / `nogc_async_mut` copies are 185/254/186-byte re-export facades. But the doc omits that `src/lib/nogc_sync_mut/terminal/__init__.spl:64` re-exports `credential_encrypt, credential_decrypt, credential_resolve` as public `std.terminal` API surface, widening who can reach it. |
| 8 | Git-history paragraph: "the working file matches `origin/main` byte-for-byte; the alias is not fresh content" | **SUPERSEDED** (was true when written) | As of 2026-08-08 `modes.spl`, `store.spl`, `__init__.spl` and `crypto/aes_gcm.spl` all DIFF from `origin/main` in the shared WC — see "In-flight work" below. |
| 9 | Blocking dependency: "newly-added stdlib functions are currently invisible to `bin/simple` under every execution engine", so a CBC fix cannot be verified | **FALSE — refuted by direct probe** | Appending an unexported `fn` to a clean stdlib file (`src/lib/common/convert.spl`) and calling it from a fresh spec inside the repo gives `SPEC FILE VERDICT: test/01_unit/lib/common/zz_audit_probe_spec.spl declared>=2 executed=2 passed=2 failed=0 dropped=0`, and from an in-repo script `bin/simple run` prints the new function's result. The symptom reproduces **only when the entry file lives outside the repo source root** — see the companion doc for the mechanism. Nothing blocks verifying a CBC fix. Probe fully reverted (`convert.spl` md5 restored to the `origin/main` blob; no `audit_probe` residue in `src/` or `test/`). |

## Severity: **High confirmed** for the defect, with exposure scoped

The security core of this report survives audit intact. Claims 1-4 — the mode
mislabel, the plaintext-derived IV, the long-lived shared key, and the
consequent keystream-reuse XOR leak that is specific to CTR — are all TRUE,
verified independently against `origin/main`. Severity stays **High**.

Scoping the exposure honestly, in both directions:

- **Not dead code.** `credential_resolve` (the decrypt half) is wired into
  real callers: `src/lib/nogc_sync_mut/terminal/ssh_terminal.spl:94,100` and
  `telnet_terminal.spl:99` resolve SSH/telnet passwords and key passphrases
  through it. The stored-credential format is live.
- **But no production caller of `credential_encrypt` was found.** Grepping
  `origin/main` across `src/**`, `scripts/**`, `examples/**` and excluding the
  credential module itself yields exactly one hit — the `export` line in
  `terminal/__init__.spl`. Nothing in-tree writes a credential today; the
  ciphertexts that `credential_resolve` reads are produced by users following
  the module's own documented example (`credential_encrypt("my_secret_password", "")`).

So the leak is real and reachable through public API, not theoretical, but
today's in-tree blast radius is the documented user-facing path rather than an
automated one. That is a reason to fix it before it acquires callers, not a
reason to downgrade it.

## What actually changes in the fix plan

Items 1 and 2 of "What a correct fix requires" were mis-scoped: the inverse
cipher and PKCS#7 padding already exist on `origin/main`, so the work is
wiring and KAT verification, not writing a block cipher from scratch. Item 3
(replace the plaintext-derived IV with a real CSPRNG IV) is the one that
carries the whole security value and is **unchanged and still required** —
note that fixing the mode to real CBC without fixing the IV leaves a genuine
vulnerability, just a quieter one. Item 4 (fix the labels) stands. The
"Why no fix here" blocker is void per claim 9.

## Relationship to the "Resolution (2026-08-08)" section above

That Resolution was written by a parallel session **while this audit was in
progress**, and it is real work: the shared WC now has a genuine CBC+PKCS#7
`modes.spl`, an `aes128/256_decrypt_block` in `crypto/aes_gcm.spl`, and a
`store.spl` that draws its IV from `rt_random_hex` (OS CSPRNG), **fails closed**
if randomness is unavailable, and reads legacy v1 records through
`aes_ctr_decrypt`. `generate_iv_from_seed` is no longer imported by `store.spl`.
Spot-checked directly; the fix addresses the actual vulnerability, not just the
label. Note its `_pkcs7_unpad_16` correctly fails *closed* rather than reusing
the fail-open `padding.spl:pkcs7_unpad`.

Two caveats that survive, and one correction the Resolution does not make:

1. **Not landed at audit time.** Every one of those files was uncommitted WC
   content; `origin/main` still had the bare CTR aliases quoted at the top of
   this doc. Claims 1-4 above were verified against `origin/main` blobs and
   describe what was actually shipped. Treat "FIXED" as true only once the
   three files are on `origin/main` — verify before relying on it.
2. **The duplicate inverse cipher stands (claim 5).** The fix implements a
   *second* AES inverse cipher in `crypto/aes_gcm.spl` while a complete
   pure-Simple one already exists in the sibling `src/lib/common/aes/cipher.spl`
   + `sbox.spl`, plus a native `rt_aes_decrypt_block_with_expanded`. That
   duplication is a direct consequence of this doc having asserted none existed.
   Deduplicating (or at minimum cross-checking the two against each other, which
   is a free extra KAT) is worthwhile follow-up.
3. **Fix-plan items 1 and 2 were mis-scoped** (claims 5a/5b) and the stated
   blocker in "Why no fix here" never existed (claim 9). Recorded so the next
   reader does not re-derive the same wrong "we must write a block cipher first"
   conclusion.

**Status after audit:** the vulnerability as shipped on `origin/main` was real
and High; a genuine fix exists and was unlanded at audit time. The stated
blocker was false.

## Known follow-ups NOT addressed by this fix

### CBC is unauthenticated — this introduces a padding oracle

`aes_cbc_decrypt` returns `nil` on invalid PKCS#7 padding and a value
otherwise, and `credential_decrypt` turns that into `""` vs. the plaintext.
That distinction is observable, which is the textbook precondition for a
padding-oracle attack, and CBC ciphertext is malleable besides (an attacker
who can write the credential file can flip chosen plaintext bits in block
N+1 by flipping bits in block N).

This is **not a regression** — the CTR that was actually running before was
equally unauthenticated and additionally leaked plaintext XORs — and the
brief for this fix specified CBC, so shipping CBC was correct. It is recorded
here so the residual weakness is not hidden by a commit labelled "security
fix". The fail-closed padding check is still strictly better than the
alternative (returning padding bytes as plaintext), so it stays.

**Correct end state: AEAD.** `aes256_gcm_encrypt`/`aes256_gcm_decrypt` are
already exported from `src/lib/common/crypto/aes_gcm.spl` — the very file this
fix extended — and are KAT-verified. A future `v3` record format should use
GCM with the credential file path or entry name as associated data, at which
point both the oracle and the malleability disappear. The versioned format
introduced here (`encrypted:v2:`) is exactly the mechanism that makes that
migration cheap: add a `v3:` marker and keep the `v2` branch read-only, the
same way `v2` keeps `v1` readable.

### `generate_iv_from_seed` is now unused but still exported

`src/lib/common/aes/utilities.spl:274` `generate_iv_from_seed` was the
deterministic LCG IV generator at the heart of this bug. `store.spl` was its
only caller and no longer uses it, so it now has zero callers in the tree. It
remains exported, and its name does not advertise that it is
cryptographically unsuitable — a footgun for the next person who needs an IV.
A deprecation banner has been added to it directing callers to the OS CSPRNG;
removing it outright is a separate API-surface decision.
