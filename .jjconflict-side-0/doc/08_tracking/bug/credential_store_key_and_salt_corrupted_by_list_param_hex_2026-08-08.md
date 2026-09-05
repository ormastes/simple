# The stored AES-256 credential key was neither the derived key nor full-entropy — `bytes_to_hex` took a `list`-spelled param

- **Filed:** 2026-08-08
- **Severity:** CRITICAL (at-rest key material corrupted and entropy-reduced)
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  underlying compiler defect stays OPEN — see
  `jit_param_passed_list_element_read_returns_tagged_2026-08-08.md`
- **Area:** `src/lib/common/aes/utilities.spl`,
  `src/lib/nogc_sync_mut/terminal/credential/store.spl`

## What was wrong

`credential_key_generate` serializes the key file as

```
val content = "{KEY_FILE_VERSION_V2}{bytes_to_hex(salt)}:{bytes_to_hex(aes_key)}"
```

so **both** the KDF salt and the 32-byte AES-256 key go through
`bytes_to_hex`. That function was declared

```
fn bytes_to_hex(bytes: list) -> text:
```

Under the seed JIT, `bytes[i]` on a param whose container is spelled `list`
(or `list<i64>`, or `list<list<i64>>`) returns the element **shifted left by
3** — arithmetically `v*8`. So every emitted byte was `(b*8) mod 256`.

## Measured (JIT, `bin/simple run`, 2026-08-08)

Probe: `bytes_to_hex(hex_to_bytes(canon))` must be an identity on `canon`.

| | value |
|---|---|
| input `canon` | `00112233445566778899aabbccddeeff` |
| **before fix** | `0088109820a830b840c850d860e870f8` — MISMATCH |
| **after fix** | `00112233445566778899aabbccddeeff` — identity |

Container-spelling table, same probe binary, `f(d) = 100 - d[3]` on
`d = [0,1,2,3,4,5]` (correct answer 97):

| param spelling | result |
|---|---|
| `list` | 76 (i.e. `100 - 24`, `3<<3`) BROKEN |
| `list<i64>` | 76 BROKEN |
| `list<list<i64>>` (`state[0][3]`) | 76 BROKEN |
| `[i64]` | 97 correct |

**Typedness is not what decides — the container spelling is.** `list<i64>` is
fully typed and breaks identically. Only `[T]` reads correctly.

### It is the VALUE's container type, not just the parameter's

Params were the first place this was seen, but the scope is wider. Measured on
a **local `val`** holding the return of `hex_to_bytes` (declared `-> list`),
with `k = hex_to_bytes("419f7f316a40bb88")`, so `k[0]` is truly `0x41` = 65:

| expression | result | correct |
|---|---|---|
| `"{k[0]}"` (interpolated/printed) | `65` | 65 |
| `k[0] % 8` | **0** | 1 |
| `(k[0] % 8) == 0` | **true** | false |
| `val e = k[0]` then `(e % 8) == 0` | **true** | false |
| `(65 % 8) == 0` (literal) | `false` | false |
| loop counting `k[i] % 8 == 0` over 8 bytes | **8** | 1 |

`65 << 3` = 520, and `520 % 8 == 0` — the shift is present in the value and
`% 8` is simply the test that exposes it. So the rule is:

> Under the seed JIT, element reads from any value whose container type is
> `list` / `list<T>` are shifted left by 3 **in arithmetic**, whether that value
> is a parameter, a local `val`, or a function return. `[T]`-typed values read
> correctly. **Interpolation and `print` untag**, so any probe that only prints
> an element reports the correct number and comes back clean.

This is why `RET_LIST_E3=3` and `DK_E0=65` looked healthy in earlier probes —
both were print-only, and print is exactly the operation that hides it. **Do not
use a printed element as evidence that a list is uncorrupted.** Use an
arithmetic oracle (`x % 8`, or a subtraction against another variable).

## Why it is a security defect, not a cosmetic one

- Every stored key byte was `≡ 0 mod 8`. The low 3 bits of each of the 32 bytes
  were forced to zero, so ~96 bits of the 256 were destroyed — roughly 160 bits
  of effective key, not 256.
- The stored key was **not the key that was derived**, so the key file did not
  hold the KDF's output at all.
- The stored **salt** was corrupted by the same call, so it did not match the
  salt actually used for derivation. Regenerating from the same passphrase on
  the same install therefore could not reproduce that install's key — which is
  the entire purpose of recording the salt.
- `bytes_to_text` (same file, same `list` spelling) is on the **decrypt** path:
  `byte.chr()` on a shifted byte decodes the wrong character for every byte.

## Why review and the spec corpus both passed it

- **The interpreter is correct on every spelling**, so `bin/simple test` is
  structurally blind: a green spec proves nothing here.
- Interpolation untags, so a probe that only `print`s a byte looks right.
- A comparison against a literal is often accidentally right (`16 > 255` is
  still false), so range guards do not fire.

## The fix

`src/lib/common/aes/utilities.spl` — `bytes_to_hex` and `bytes_to_text` now
take `[i64]`. Passing a `list`-typed value (e.g. the return of `hex_to_bytes`,
which is still declared `-> list`) into an `[i64]` param is measured correct;
it is the **param spelling on the callee**, not the caller's value, that
matters.

## Positive control

1. Pre-fix probe: `RT_MATCH=false`, `RT_HEX=0088109820a830b840c850d860e870f8`.
2. Sabotage `bytes_to_hex` to `return "SABOTAGE_MARKER_7731"` → probe printed
   `RT_HEX=SABOTAGE_MARKER_7731`, proving `bin/simple run` was serving the
   edited `src/lib/` tree and not a bundled stdlib.
3. Post-fix probe: `RT_MATCH=true`, and the end-to-end key file is well-formed
   (`v2:` + 32 hex salt + `:` + 64 hex key, 100 chars), `credential_load_key`
   returns the exact 32 bytes that `credential_derive_key` produced
   (`KEY_SERIALIZE_FIDELITY=true`), and encrypt→decrypt round-trips.

## Not fixed here — the enumerated family

The same corrupting spelling is used pervasively on the AES and bcrypt paths
and each occurrence is the same latent defect. Enumerated so no sibling is left
behind:

- `src/lib/common/aes/cipher.spl` — 21 fns (`shift_rows`, `mix_columns`,
  `add_round_key`, `aes_encrypt_block`, `aes_decrypt_block`, …), all `list`
- `src/lib/common/aes/key_expansion.spl` — 6 fns, all `list`
- `src/lib/common/aes/sbox.spl` — 3 fns; `src/lib/common/aes/types.spl` — 4 fns
- `src/lib/common/aes/utilities.spl` — remaining `list` fns: `xor_blocks`,
  `xor_bytes_list`, `print_state`, `print_block`, `blocks_equal`,
  `compute_checksum`, `add_checksum`, `verify_checksum`
- `src/lib/common/bcrypt/{hash,key_derivation,salt,types}.spl` — 13 fns, all
  `list<i64>` / `list<list<i64>>`, including the whole Eksblowfish state
- `src/lib/nogc_sync_mut/terminal/credential/store.spl:225`
  `credential_derive_key(salt: list[i64], …) -> list[i64]`

`bcrypt_encode_base64` / `encode_salt` are already filed by a sibling lane; the
bcrypt CSPRNG fix is unaffected and holds.

## What this fix does NOT make sound — read before trusting the store

Only the at-rest **encoding** is repaired. The **KDF input path is still
corrupted** under the seed JIT:

- `hex_to_bytes` is declared `-> list`, so `credential_load_key` hands the AES
  path a `list`-typed key whose element arithmetic is shifted.
- `credential_derive_key(salt: list[i64], …)` forwards the salt into
  `eksblowfish_setup(… list<i64> …)`, and the entire bcrypt/Eksblowfish tree
  uses the broken spelling.

An encrypt → decrypt round-trip returning `true` does **not** refute this: both
directions are corrupted identically, so the test is self-consistent and blind.
The correct reading of this fix is "the key file now records exactly the bytes
the KDF produced", not "the KDF produces the right bytes".

## Scope

Seed-JIT defect. Pure-Simple native codegen is measured CLEAN on every
spelling. It has full operational reach anyway, because `bin/simple` **is** the
seed today, so the corrupted key file is a real artifact of the current
toolchain.

## Related

- `doc/08_tracking/bug/jit_param_passed_list_element_read_returns_tagged_2026-08-08.md` (root cause, OPEN)
- `doc/08_tracking/bug/credential_key_generate_random_hex_length_reads_shifted_2026-08-08.md`
- `doc/08_tracking/bug/rt_package_chmod_family_fails_from_jit_key_left_world_readable_2026-08-08.md`
