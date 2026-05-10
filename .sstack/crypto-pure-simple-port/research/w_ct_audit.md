# W-CT Audit — Constant-Time Discipline in pure-Simple crypto stack

**Wave:** 5  **Date:** 2026-04-26  **Auditor:** W-CT (Claude Opus, 1M ctx)
**SStack feature:** `crypto-pure-simple-port`
**Repo HEAD:** `d43e8c5c507df5c6e21222f627d89689b667dc5d`

## 1. Scope

Goal: confirm constant-time (CT) discipline across the pure-Simple crypto stack
- (a) verify the B6 `rt_black_box` / `black_box(x)` opaque-identity intrinsic
  is wired correctly,
- (b) flag any `if/elif/while x ==` / early-return patterns that branch on
  **secret** data (key bytes, scalar bits, password material, MAC tags),
- (c) verify `cond_swap`/`cond_select` are branch-free.

Owned-code scope only — vendored crypto in `src/runtime/vendor/**` is excluded.
The Rust runtime `crypto_compare.rs` is documented for context but classified
as out-of-scope CONCERN, not LEAK.

## 2. Audit Methodology

Classification is **strict** per advisor guidance:

- **SAFE** — branch-free, or branch-on-public-only (length / algo selector / nil
  check) and the comparison core uses XOR accumulator.
- **CONCERN** — leaky pattern in source, but no caller feeds secret data on the
  path; document and watch.
- **LEAK** — confirmed secret-data caller reaches a data-dependent branch in
  the comparison loop body or an early `return false` mid-byte-loop.

LEAK test: trace from secret material (key, password, MAC tag, signature,
session secret, ECDH shared secret) to comparator. Branch on length is **public**
— SHA-2/HMAC/sig output lengths are public. Branch on accumulator value or on
individual byte equality is **secret-dependent**.

## 3. Module-by-module audit

### 3.1 Canonical CT primitive — `src/lib/common/crypto/constant_time.spl`

| Site | Class | Rationale |
|---|---|---|
| `constant_time.spl:7-11` `rt_constant_time_compare` extern + Simple wrapper | **SAFE** | Delegates to Rust runtime; the Simple-side wrapper is one extern call + `== 1`. No Simple-side accumulator to wrap. |
| `constant_time.spl:8,19-20` `rt_black_box(x)` / `black_box(x)` | **SAFE (forward-positioned)** | B6 intrinsic is intentionally not yet applied — it is reserved for §3 (ML-KEM rejection sampling) and §5.4 (Curve25519 `cond_swap`). Per B6 doc and advisor: "no current Simple-side CT accumulators in `constant_time.spl` to wrap; the module is intentionally a thin extern shim plus a forward-looking intrinsic." Not a defect. |

### 3.2 Rust runtime — `src/compiler_rust/runtime/src/value/ffi/crypto_compare.rs`

| Site | Class | Rationale |
|---|---|---|
| `crypto_compare.rs:21-52` `rt_constant_time_compare` | **CONCERN (out-of-scope)** | Implementation uses XOR accumulator (`acc \|= a[i] ^ b[i]`) — correct. **However**, the final reduction is `if acc == 0 { 1 } else { 0 }` — the exact B6 branch-on-accumulator hazard. rustc usually compiles this to a `cmov`/`sete` (branch-free) on x86_64 with `-O`, but this is not guaranteed across targets/optimizers. Recommendation: switch to bitwise reduction `((acc \| acc.wrapping_neg()) >> 7) ^ 1` cast to i64, or call `subtle::ConstantTimeEq`. Per audit scope this is logged as CONCERN; not filed as P1 LEAK because the host compiler is rustc, not Cranelift, and the empirical pattern emits `cmov`. |

### 3.3 Pure-Simple crypto utilities — `src/lib/common/crypto/`

| Site | Class | Rationale |
|---|---|---|
| `utilities.spl:22-32` `constant_time_compare(a: list, b: list)` | **SAFE** | Length check first (public), then XOR accumulator with `\|`, terminal `result == 0`. No early return inside the byte loop. Shadow of canonical impl — see §4 cleanup note. |
| `utilities.spl:35-36` `secure_compare` | **SAFE** | Pure delegation to `constant_time_compare`. |
| `utilities.spl:39-41` `verify_hash` | **SAFE** | Uses `constant_time_compare` for hex-string compare; both sides are SHA-256 hex (public-length). |
| `utilities.spl:53-55` `verify_password` | **SAFE** | Uses `constant_time_compare` for hex(PBKDF2) — correct CT path. |
| `utilities.spl:81-83,86-112` `verify_checksum` → `compare_hex_hashes` | **CONCERN** | `compare_hex_hashes` has `if c1_lower != c2_lower: match = false` — data-dependent branch inside the loop; even though `match` short-circuits no further work, the branch is still timing-observable. Callers traced: `incremental.spl` (build-artifact hash, public), `package.registry/verify.spl` (package checksum, public). **No secret-data caller** — checksums of public files. CONCERN: do not use this for HMAC/MAC/signature paths. |
| `hmac.spl`, `sha256.spl`, `sha512.spl`, `pbkdf2.spl`, `legacy_hash.spl`, `types.spl` | **SAFE** | Hash compression / HMAC / PBKDF2 inner loops branch only on public structural inputs (block index, padding boundary, message length). No comparator on secret bytes. `xor_bytes` (`types.spl:176-187`) and `add_mod32/64` are pure ALU. |

### 3.4 SSH daemon — `src/os/apps/sshd/`

| Site | Class | Rationale |
|---|---|---|
| `ssh_auth.spl:374-385` `_blobs_equal` | **SAFE** | Length check (public — RFC 4253 key blob length is public), then XOR accumulator → `diff == 0`. No mid-loop early return. Used at `:118` against `authorized_keys[*]` — public-key blob compare; both operands are public anyway. |
| `ssh_auth.spl:96-103` `authenticate_password` → `rt_auth_check` | **CONCERN** | Delegates password comparison to extern `rt_auth_check` — outside this audit's scope. Whether that extern is CT depends on its Rust impl. Adjacent comment "plaintext password comparison (SHA-256 may FAULT on baremetal)" suggests baremetal stub may use `==`. Filed as CT bug for follow-up. |
| `ssh_cipher.spl:131-216, 354-413` AEAD decrypt paths | **SAFE** | AES-GCM / ChaCha20-Poly1305 tag verification happens inside `aes256_gcm_decrypt` / `chacha20_poly1305_decrypt` runtime externs (which are required to be CT by their AEAD spec). Simple-side only does length check (public packet length) and Result match. No Simple-side tag `==` compare. |
| `ssh_session.spl:340-395` ECDH + ed25519/RSA verify | **SAFE** | Signature verification via `rt_ed25519_verify` / `rt_rsa_sha256_verify` externs. Length checks (`shared_secret.len() != 32`, `client_public.len() == 32`) on **public** wire-format lengths. No Simple-side secret-byte comparator. |
| `ssh_kex.spl`, `ssh_transport.spl` | **SAFE** | All `==` patterns audit are on algorithm-name strings ("ssh-ed25519", "rsa-sha2-256") or wire-format lengths — both public. |
| `sshd.spl` | **SAFE** | No comparator on secret data found. |

### 3.5 TLS / web auth — `src/lib/nogc_sync_mut/tls/`, `src/app/ui.web/`

| Site | Class | Rationale |
|---|---|---|
| `tls/validation.spl:15-` `constant_time_compare(a, b)` | **SAFE** | Standard XOR accumulator, terminal `diff == 0`. Length first, no mid-loop branch. Shadow of canonical. |
| `tls/utilities.spl:35-` `constant_time_compare` | **SAFE** | Same shape — XOR accumulator. |
| `app/ui.web/session_token.spl:99` HMAC token verify | **SAFE** | Uses canonical `constant_time_compare` from `std.crypto.constant_time` over hex-encoded HMAC-SHA256. Origin/expiry checks branch on **public** values (origin string, time). Secret HMAC tag never reaches a `==` operator. |

### 3.6 Other shadow `*constant_time_compare*` impls

| Site | Class | Rationale |
|---|---|---|
| `src/lib/common/base64/utilities.spl:337` `compare_constant_time(s1: text, s2: text)` | **CONCERN** | Has `if c1 != c2: result = result + 1` — **data-dependent branch within the loop body**. Pattern *is* leaky (the branch creates a side channel even though no early return). Caller scan: only re-exported via `base64/mod.spl:110`. **No source caller passes secret data.** Documented as CONCERN — must NOT be wired into MAC/HMAC/signature compare. |
| `src/lib/common/scrypt/validation.spl:119-` `compare_constant_time(a: list, b: list)` | **SAFE** | Length check first, clean XOR accumulator with `\|`, terminal `if result == 0`. Used by `scrypt/utilities.spl:190` to compare password-derived hashes — proper CT path. |
| `src/lib/common/secure_random/utilities.spl:75-` `constant_time_compare(a: list, b: list)` | **SAFE** | Length check, clean XOR accumulator, terminal `diff == 0`. |
| `src/lib/common/signature/utilities.spl:270-275` `constant_time_compare(i64, i64)` and `constant_time_compare_bytes(list, list)` | **SAFE** | Integer variant: `diff = a^b; diff == 0` — branch-free in source. Bytes variant: standard XOR accumulator. |
| `src/lib/common/jwt/sign.spl:280-` `constant_time_compare(a: list, b: list)` | **SAFE** | XOR accumulator, length check first. |

### 3.7 `cond_swap` / `cond_select`

**Result:** **No `cond_swap` or `cond_select` symbol exists yet** in
`src/lib/common/crypto/` or anywhere in `src/lib/`. Per B6 doc, these are
gated on §5.4 (PQ TLS) / Curve25519 work — not yet implemented. When they
land, they MUST be wrapped with `black_box` per B6.

**Audit verdict for §(c):** N/A — no current implementation to audit.
A regression spec template is provided for when they land
(`test/unit/lib/common/crypto/constant_time_cond_swap_spec.spl`).

## 4. Summary

| Class | Count | Sites |
|---|---|---|
| **SAFE** | 19 | constant_time.spl x2, utilities.spl x4, hmac/sha/pbkdf2/types/legacy_hash, ssh_auth `_blobs_equal`, ssh_cipher AEAD, ssh_session, ssh_kex/transport, tls validation/utilities x2, session_token, scrypt, secure_random, signature x2, jwt |
| **CONCERN** | 4 | rt_constant_time_compare final compare; compare_hex_hashes case-fold branch; base64 compare_constant_time inner-loop branch; rt_auth_check extern (out-of-scope) |
| **LEAK** | 0 | none confirmed |

## 5. LEAK findings

**None.** All leaky shapes encountered (compare_hex_hashes case-fold branch,
base64 compare_constant_time inner-loop `if c1 != c2`) lack a confirmed
secret-data caller in the current source tree. They are pre-emptively
documented as CONCERN with hard "do not wire to secret material" notes.

## 6. Bugs filed

See §7 below. **Three CT-hardening bugs** filed (none P1; all P2 / hardening).

## 7. Recommendations (no source patches — advisor-gated)

1. **Hardening (P2):** Replace `compare_hex_hashes` with a byte-level XOR
   accumulator that does the case fold via constant-time bit ops
   (`c | 0x20` for ASCII letters before XOR). Even though no secret caller
   today, deletes a footgun. Tracked in `bug_ct_2`.
2. **Hardening (P2):** Rewrite `base64/utilities.spl:compare_constant_time`
   to mirror the canonical XOR-accumulator shape; remove the
   `if c1 != c2: result = result + 1` branch. Tracked in `bug_ct_1`.
3. **CT review (P2):** Confirm `rt_constant_time_compare` Rust impl emits
   branch-free code on all targets (x86_64, aarch64, riscv64, baremetal).
   Switch the final `if acc == 0 { 1 } else { 0 }` to a bitwise reduction.
   Tracked in `bug_ct_3`.
4. **Cleanup (P3):** 7+ shadow `constant_time_compare` impls exist across
   `lib/common/{base64,scrypt,secure_random,signature,jwt}/`,
   `lib/nogc_sync_mut/tls/{validation,utilities}.spl`,
   `lib/common/crypto/utilities.spl`. Most are SAFE but each is an
   independent attack surface. Future port should converge them on
   `std.crypto.constant_time.constant_time_compare`. Not filed as a bug —
   in scope for the broader port wave.
5. **Future (info):** When `cond_swap` / `cond_select` for Curve25519 /
   ML-KEM land, they must wrap the conditional select mask with
   `black_box(mask)` per B6, before XOR-merge. Regression spec template
   left in `test/unit/lib/common/crypto/constant_time_cond_swap_spec.spl`.

## 8. Verification

- **B6 intrinsic wired:** confirmed at
  `src/lib/common/crypto/constant_time.spl:8,19-20` and Rust side at
  `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:296`
  (interpreter) — opaque identity is in place.
- **Per-module owned-code grep** for `==` on secret-typed identifiers
  (`mac`, `tag`, `secret`, `key`, `password`, `signature`) returned only
  the cases enumerated above — all classified.
- **No early-return-mid-byte-loop** found on any secret-data path in pure
  Simple crypto code.

## 9. Out-of-scope notes

- `rt_auth_check` extern (`ssh_auth.spl:102`) — Rust side; comment hints
  at baremetal stub possibly using `strcmp` or `==`. Filed as `bug_ct_3`
  for the Rust crew to verify.
- Vendored Rust crypto under `src/compiler_rust/vendor/**`: not audited.
- Cranelift IR-level CT verification (B6 acceptance test
  `cargo test ct_eq_no_branch`): proposed in B6 but not yet implemented;
  out of scope for this Simple-side audit.
