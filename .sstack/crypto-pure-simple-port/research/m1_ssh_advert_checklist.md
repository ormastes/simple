# M1 — SSH Modern-Algorithm Advert: Implementation Checklist

Date: 2026-04-25
Source plan: `doc/08_tracking/todo/ssh_tls_modern_algorithms_2026-04-25.md` §1.1–§1.5
Reconciliation: `.sstack/crypto-pure-simple-port/research/m_status.md` (R-A)
Author: R-E (research, read-only)

> **Scope:** M1 only (SSH advert + Terrapin reset + ECDSA host-key blob + EXT_INFO).
> **Out of scope (M2):** ETM MACs, OpenSSH cert host keys, FIDO/SK auth — do not bundle.

---

## 1. TL;DR

M1 lifts the sshd from "advertises one cipher (`aes128-gcm@openssh.com`), one host-key family, no MAC, no `ext-info`" to OpenSSH-9-default-class advert: AES-256-GCM preferred, AES-128-GCM kept, `chacha20-poly1305@openssh.com` fallback, host keys `rsa-sha2-512,rsa-sha2-256,ssh-ed25519,ecdsa-sha2-nistp256` (with the ECDSA blob actually built), Terrapin strict-kex (`kex-strict-s-v00@openssh.com`) with seq-counter reset after NEWKEYS and rejection of pre-KEX `IGNORE`/`DEBUG`, and a server-sent `SSH_MSG_EXT_INFO` carrying `server-sig-algs`.

**Already done (visible in tree):**
- `curve25519-sha256` KEX advertised, `ext-info-s` token advertised in KEX list.
- `aes128-gcm@openssh.com` cipher implemented + RFC-correct framing (working copy `ssh_encrypt_packet_aes_gcm` rewrite — preserve it).
- `rsa-sha2-256` + `ssh-ed25519` host-key sign paths.
- `kex-strict-s-v00@openssh.com` token already in `KEX_ALGORITHM` literal — but no Terrapin sequence-counter reset / pre-KEX message rejection wired.

**Missing for M1:** AES-256-GCM order/code path; ChaCha20-Poly1305 advert wiring; Terrapin runtime behaviour (counter reset + reject); `rsa-sha2-512` advert; ECDSA-P256 host-key blob builder body; `ssh-ed25519` reorder; `SSH_MSG_EXT_INFO` builder + send-after-NEWKEYS.

---

## 2. Algorithm List

| Slot | Today (`ssh_transport.spl`) | M1 target | RFC / spec | Action |
|------|-----------------------------|-----------|-----------|--------|
| KEX | `curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com` | `curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com` (unchanged tokens — but add runtime behaviour) | RFC 8731; RFC 8308; OpenSSH PROTOCOL §1.9 (Terrapin) | wire Terrapin reset |
| Host-key | `rsa-sha2-256,ssh-ed25519` | `rsa-sha2-512,rsa-sha2-256,ssh-ed25519,ecdsa-sha2-nistp256` | RFC 8332; RFC 8709; RFC 5656 | advertise + finish ECDSA blob |
| Cipher (c2s & s2c) | `aes128-gcm@openssh.com` | `aes256-gcm@openssh.com,aes128-gcm@openssh.com,chacha20-poly1305@openssh.com` | RFC 5647; OpenSSH PROTOCOL.chacha20poly1305 | reorder + add chacha20 (impl already present, just advertise) |
| MAC | `none` | `none` (M1) | — | unchanged (ETM is M2) |
| Compression | `none` | `none` | — | unchanged |
| EXT-INFO | not sent | `SSH_MSG_EXT_INFO {server-sig-algs: rsa-sha2-512,rsa-sha2-256,ssh-ed25519,ecdsa-sha2-nistp256}` after first NEWKEYS | RFC 8308 §2, §3.1 | new builder + send hook |

> Verify before edit: confirm `ssh_cipher.spl` actually has `aes256-gcm` and `chacha20-poly1305` impls. Plan §1.1/§1.2 says "advertise what we already have" — if either body is missing, downgrade the task to "implement+advertise" and flag.

---

## 3. Per-File Change Checklist (ordered by dependency)

> Order rule: probe support → then advertise → then negotiate → then post-NEWKEYS extras.

### Step 0 — Pre-flight probe (no edits)
- [ ] **0.a** Grep `src/os/apps/sshd/ssh_cipher.spl` for `aes256_gcm_encrypt`, `aes256_gcm_decrypt`, `chacha20_poly1305_encrypt`, `chacha20_poly1305_decrypt`. **Acceptance:** all four exist; if not, file a separate todo and reduce M1 advert to what's actually implemented. **Size:** xs.
- [ ] **0.b** Grep `src/os/apps/sshd/ssh_kex.spl` for `_build_host_key_blob_for_algo`. Confirm ECDSA arm returns `[]` (per plan). **Acceptance:** stub confirmed. **Size:** xs.
- [ ] **0.c** Confirm a P-256 ECDSA sign extern exists (`rt_ecdsa_p256_sign` or equivalent). If absent, ECDSA advert (§1.4) becomes contingent. **Size:** xs.
- [ ] **0.d** Read working-copy diff (`git diff src/os/apps/sshd/`). Note: `ssh_cipher.spl` GCM-framing rewrite, `ssh_auth.spl` byte-literal workaround (H-9 candidate), `ssh_kex.spl` log-import swap, `rt_net_recv_ssh_encrypted_packet` extern. **Do not regenerate any of these from origin/main.** **Size:** xs.

### Step 1 — Cipher list reorder + chacha (§1.1, §1.2)
- [ ] **1.a** Edit `src/os/apps/sshd/ssh_transport.spl` constant `CIPHER_ALGORITHM` from `"aes128-gcm@openssh.com"` to `"aes256-gcm@openssh.com,aes128-gcm@openssh.com,chacha20-poly1305@openssh.com"`. **Acceptance:** `ssh_build_kexinit()` payload includes the three names in order. **Size:** xs.
- [ ] **1.b** Verify `ssh_negotiate_algorithms` picks the first common entry — no behavioural change needed if it does; otherwise update picker. **Acceptance:** unit test feeding a client list `aes256-gcm@openssh.com,aes128-gcm@openssh.com` returns `aes256-gcm@openssh.com`. **Size:** s.
- [ ] **1.c** **(Critical — not a side-quest.)** Wire encrypt/decrypt dispatch on negotiated cipher name in `ssh_cipher.spl`. The current entry point (`ssh_encrypt_packet_aes_gcm` / `ssh_decrypt_packet_aes_gcm`) is hard-coded to AES-128-GCM; advertising aes256-gcm + chacha20 without a name-keyed dispatch ships negotiation success + encryption failure. Add `ssh_encrypt_packet(algo: text, ...)` switching on `algorithms.cipher_s2c` to the appropriate primitive (preserving the AAD/block-aligned framing rewrite from WC). **Acceptance:** unit round-trips for all three negotiated ciphers; OpenSSH client successfully completes a handshake under each `-oCiphers=` from Step 5. **Size:** m. **Do not bundle 1.a/1.b/1.c into a single "advert" commit.**

### Step 2 — Host-key advert + ECDSA blob (§1.4)
- [ ] **2.a** Edit `HOST_KEY_ALGORITHM` in `ssh_transport.spl` to OpenSSH-9 server default order: `"ssh-ed25519,ecdsa-sha2-nistp256,rsa-sha2-512,rsa-sha2-256"`. (Modern-key-first is the OpenSSH 9 default; the existing WC literal `"rsa-sha2-256,ssh-ed25519"` is legacy and will be replaced.) **Acceptance:** appears in KEXINIT name-list in that exact order. **Size:** xs.
- [ ] **2.b** In `ssh_kex.spl`, complete `_build_host_key_blob_for_algo` ECDSA arm: emit `string "ecdsa-sha2-nistp256" || string "nistp256" || string Q` where `Q = 0x04 || X || Y` (uncompressed SEC1, 65 bytes). RFC 5656 §3.1. **Acceptance:** blob length 104 bytes for sample key; KAT against OpenSSH-extracted blob. **Size:** s.
- [ ] **2.c** Wire `_sign_ecdsa_p256` (call `rt_ecdsa_p256_sign` returning DER signature, then re-encode as SSH `string "ecdsa-sha2-nistp256" || string (mpint r || mpint s)` per RFC 5656 §3.1.2). **Acceptance:** sign-then-verify against `rt_ecdsa_p256_verify_der` returns 1. **Size:** m.
- [ ] **2.d** Add `set_host_ecdsa_key()` setter on `SshDaemon` (mirror `set_host_rsa_key`) and gate ECDSA advert on its presence. **Acceptance:** sshd without ECDSA key drops `ecdsa-sha2-nistp256` from advert. **Size:** s.
- [ ] **2.e** Add `rsa-sha2-512` sign path: hash with SHA-512 instead of SHA-256, emit signature blob with format-id `rsa-sha2-512`. RFC 8332 §3. **Acceptance:** test vector signs+verifies. **Size:** s.

### Step 3 — Terrapin / strict-kex (§1.3)
- [ ] **3.a** In `ssh_session.spl`, after sending+receiving NEWKEYS, set `seq_c2s = 0` and `seq_s2c = 0` *only* when the negotiated KEX list contained `kex-strict-s-v00@openssh.com` from both sides. OpenSSH PROTOCOL §1.9. **Acceptance:** unit test asserts seq counters reset to 0 post-NEWKEYS in strict mode and *not* reset in non-strict mode. **Size:** s.
- [ ] **3.b** Reject `SSH_MSG_IGNORE` (2), `SSH_MSG_DEBUG` (4), `SSH_MSG_UNIMPLEMENTED` (3) received between version exchange and NEWKEYS when strict-kex is active — disconnect with reason `SSH_DISCONNECT_KEY_EXCHANGE_FAILED` (3). **Acceptance:** session test sends pre-KEX `IGNORE` → server disconnects with reason 3. **Size:** s.
- [ ] **3.c** Confirm `KEX_ALGORITHM` already contains `kex-strict-s-v00@openssh.com` token (it does per current literal) and that the negotiator records "strict mode" on both-sides match. **Acceptance:** boolean `algorithms.strict_kex == true` when client also offered the token. **Size:** xs.
- [ ] **3.d** **First-KEX only.** OpenSSH PROTOCOL §1.9: the strict-kex token must appear in the *initial* KEXINIT only; advertising it during a rekey is spoofable. Suppress the token from any KEXINIT built after the first NEWKEYS has been sent. **Acceptance:** rekey-triggered KEXINIT payload omits `kex-strict-s-v00@openssh.com`. **Size:** xs.

### Step 4 — EXT_INFO (§1.5)
- [ ] **4.a** Add `SSH_MSG_EXT_INFO: u8 = 7` to `ssh_transport.spl` constants. **Size:** xs.
- [ ] **4.b** New file `src/os/apps/sshd/ssh_extinfo.spl`. Function `ssh_build_ext_info(extensions: [(text, text)]) -> [u8]`: byte `SSH_MSG_EXT_INFO` (imported from `ssh_transport`, **not** re-declared here — avoid circular-redef wedges), `uint32 nr-extensions`, then per-extension `string ext-name || string ext-value`. RFC 8308 §2.3. **Acceptance:** byte-exact match against RFC 8308 §3.1 example. **Size:** s.
- [ ] **4.c** In `ssh_session.spl`, immediately after sending the server's NEWKEYS (and after Terrapin reset if strict), if the parsed client KEXINIT advertised `ext-info-c`, send one EXT_INFO with `server-sig-algs = "rsa-sha2-512,rsa-sha2-256,ssh-ed25519,ecdsa-sha2-nistp256"`. **Acceptance:** OpenSSH client log shows `kex_ext_info_check_ver: ssh-rsa=, rsa-sha2-256=, rsa-sha2-512=`. **Size:** s.
- [ ] **4.d** Add `ext-info-s` is already in `KEX_ALGORITHM` — verify; if a client sends `ext-info-c` we still send EXT_INFO regardless (RFC 8308 says server advertises `ext-info-s`, sends if client advertised `ext-info-c`). **Size:** xs.

### Step 5 — Wiring + smoke
- [ ] **5.a** Run baremetal sshd self-test in QEMU (existing infrastructure) — handshake completes with ssh-keygen-generated client. **Size:** s.
- [ ] **5.b** Update `doc/06_spec/generated/feature.md` regen via `bin/simple test`. **Size:** xs.

---

## 4. KAT Vectors Needed

| Vector | Source | Test landing |
|--------|--------|--------------|
| Curve25519 KEX hash (`H = HASH(V_C || V_S || I_C || I_S || K_S || Q_C || Q_S || K)`) sample | RFC 4253 §8 + RFC 8731 §3 | `test/unit/os/apps/sshd/ssh_kex_hash_spec.spl` |
| `aes256-gcm@openssh.com` packet encrypt KAT | RFC 5647 §5 | `test/unit/os/apps/sshd/ssh_aes256_gcm_packet_spec.spl` |
| `chacha20-poly1305@openssh.com` packet encrypt KAT | OpenSSH PROTOCOL.chacha20poly1305 | `test/unit/os/apps/sshd/ssh_chacha20_poly1305_packet_spec.spl` |
| `ecdsa-sha2-nistp256` host-key blob byte layout | RFC 5656 §3.1 | `test/unit/os/apps/sshd/ssh_ecdsa_p256_blob_spec.spl` |
| `rsa-sha2-512` signature format | RFC 8332 §3 | `test/unit/os/apps/sshd/ssh_rsa_sha2_512_spec.spl` |
| EXT_INFO `server-sig-algs` byte layout | RFC 8308 §3.1 (matches example) | `test/unit/os/apps/sshd/ssh_ext_info_spec.spl` |
| Terrapin strict-kex seq-counter reset | OpenSSH PROTOCOL §1.9 | `test/unit/os/apps/sshd/ssh_terrapin_strict_kex_spec.spl` |

> Test directory `test/unit/lib/common/crypto/` does **not** exist today (verified). All new specs go under `test/unit/os/apps/sshd/`.

---

## 5. Interop Test Recipe

Daemon launch: `bin/simple src/app/test/sshd_test_runner.spl --port 2222` (or whichever existing baremetal/userland harness — confirm at impl time).

Client probes:

```bash
# AES-256-GCM preferred
ssh -v -p 2222 -o StrictHostKeyChecking=no \
    -o KexAlgorithms=curve25519-sha256 \
    -o HostKeyAlgorithms=ssh-ed25519 \
    -o Ciphers=aes256-gcm@openssh.com \
    -o MACs=none \
    user@127.0.0.1 exit

# ChaCha20-Poly1305 fallback
ssh -v -p 2222 -o Ciphers=chacha20-poly1305@openssh.com user@127.0.0.1 exit

# ECDSA host key
ssh -v -p 2222 -o HostKeyAlgorithms=ecdsa-sha2-nistp256 user@127.0.0.1 exit

# rsa-sha2-512
ssh -v -p 2222 -o HostKeyAlgorithms=rsa-sha2-512 user@127.0.0.1 exit

# Strict KEX (Terrapin)
ssh -v -p 2222 -o StrictKex=yes user@127.0.0.1 exit
```

Expected `-v` line fragments (handshake success):
- `kex: algorithm: curve25519-sha256`
- `kex: host key algorithm: <one of advert>`
- `kex: server->client cipher: aes256-gcm@openssh.com MAC: <implicit> compression: none`
- `kex_input_ext_info: ... server-sig-algs=<ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256>`
- (strict) `expecting SSH2_MSG_KEX_ECDH_REPLY` with no intervening `SSH2_MSG_IGNORE` warnings; `kex_input_strict_kex` accepted.

---

## 6. Risks (working-copy reconciliation)

A future implementer **must reconcile** these uncommitted edits before / during M1:

1. **`ssh_cipher.spl` GCM packet-framing rewrite (uncommitted, RFC-correct).** §1.1/§1.2 reorder the cipher list — keep the new `payload_len`/`packet_length` math; do not regenerate the function from `origin/main`. M_STATUS Risk #2.
2. **`ssh_auth.spl` byte-literal workaround for `"publickey,password,keyboard-interactive"`.** A real text-encoding bug (H-9 candidate). File a `doc/08_tracking/bug/` entry; do **not** silently delete — it breaks userauth fail responses on baremetal until the underlying `ssh_put_text` issue is fixed. M_STATUS Risk #1.
3. **`ssh_kex.spl` + `ssh_session.spl` log-API swap (`os.kernel.log.klog_api` → `os.userlib.log`) plus new `rt_net_recv_ssh_encrypted_packet` extern.** Must stay paired with the GCM-framing fix; partial commits break userland sshd build. M_STATUS Risk #3. Step 4.c lands edits in `ssh_session.spl` — preserve the import swap.
4. **No `class` inside `it` in tests, no `skip()` keyword.** B3-residuals R1/R2 still affect `--mode=smf`. Run M1 specs in interpret mode unless proven SMF-clean.
5. **`crypto_spec_remains_2026-04-16.md` Issue #1 (Poly1305 finalize tag byte[0])** — re-verify before declaring chacha20-poly1305 advert healthy; could surface as KAT failure on §1.2.
6. **`crypto_spec_remains_2026-04-16.md` Issue #2 (interpreter wraps FFI sign returns in `Option<[u8]>`).** Will affect the new `rsa-sha2-512` sign path (Step 2.e) under the interpreter; compiled mode required for spec verification. (Cranelift `>>` is fixed per FR-DRIVER-0002b.)
7. **No branches; jj only.** Land per-step commits — do not bundle Steps 1–4 into one "feat: M1" snapshot. Per-phase commits per `feedback_sync_bundling_clobbers_commits`.
8. **After any new `rt_*` extern (Step 0.c if ECDSA sign ext is missing), run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`** — `bin/simple build bootstrap` no-ops via wrapper whitelist (`feedback_extern_bootstrap_rebuild`).

---

## Owner

Unassigned. Cold-pickup ready: Step 0 → Step 5 in order; per-step jj commits.
