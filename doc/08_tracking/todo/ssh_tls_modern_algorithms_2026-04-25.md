# SSH + TLS Modern Algorithm Rollout (Pure Simple)

Date: 2026-04-25
Owner: unassigned
Scope: Implement the missing modern algorithms in pure Simple (no OpenSSL FFI),
wire them into `src/os/apps/sshd/` and the HTTPS/web-server path, and track
every compiler/interpreter bug or perf regression that surfaces during the work.

Audit of current state: see the sibling finding at the top of `doc/08_tracking/todo/`
(conversation 2026-04-25) — SSH offers only `curve25519-sha256` + AEAD + none/none;
`tls/types.spl:35-41` defines only seven TLS 1.2 suites; no TLS 1.3, no PQ, no
HTTPS wiring in `src/app/ui.web/server.spl`.

Golden rule while porting: **fix the compiler, don't work around it.** Every
ugly shape added to avoid a compiler bug goes in §6 as a real bug entry with a
minimal repro, not as a silent workaround (per CLAUDE.md).

---

## 1 · SSH — Advertise what we already have (fast wins)

| # | Task | Files | Acceptance |
|---|------|-------|-----------|
| 1.1 | Advertise `aes256-gcm@openssh.com` ahead of `aes128-gcm@openssh.com` | `ssh_transport.spl` `CIPHER_ALGORITHM` | OpenSSH client negotiates AES256-GCM |
| 1.2 | Advertise `chacha20-poly1305@openssh.com` as fallback | same | Client negotiates ChaCha20-Poly1305 when forced |
| 1.3 | Advertise `kex-strict-s-v00@openssh.com` + apply Terrapin countermeasure (reset seq=0 after NEWKEYS; reject unexpected IGNORE/DEBUG before KEX) | `ssh_transport.spl`, `ssh_session.spl` | `ssh -o StrictKex=yes` connects cleanly, mitigation verified by test |
| 1.4 | Finish ECDSA `ecdsa-sha2-nistp256` host-key blob in `_build_host_key_blob_for_algo` (currently returns `[]`) | `ssh_kex.spl` | ECDSA host key loads and signs EX hash |
| 1.5 | Advertise `ext-info-s` + send `SSH_MSG_EXT_INFO` with `server-sig-algs` | new `ssh_extinfo.spl`, `ssh_session.spl` | Client receives and uses `rsa-sha2-512` |

## 2 · SSH — New symmetric / MAC primitives (pure Simple)

| # | Task | New file(s) | Acceptance |
|---|------|-------------|-----------|
| 2.1 | `hmac-sha2-256-etm@openssh.com` + `hmac-sha2-512-etm@openssh.com` (ETM, CBC/CTR cipher pairs) | `ssh_mac.spl`, reuse `common/crypto/hmac.spl` | ETM round-trip test + negotiation |
| 2.2 | `aes256-ctr` fallback cipher | `ssh_cipher.spl` | Round-trip with OpenSSH |
| 2.3 | Compression `zlib@openssh.com` (deflate + inflate) | `common/compression/zlib.spl` (may already exist — check) | Enabled connection transfers smaller payload |

## 3 · SSH — Post-quantum / hybrid KEX

| # | Task | Algorithm | Dependencies | Acceptance |
|---|------|-----------|--------------|-----------|
| 3.1 | ML-KEM-768 (FIPS 203) reference impl | Keccak/SHAKE-128/256, NTT over Z/3329 | §5.1 SHA-3 | KAT vectors from NIST pass |
| 3.2 | `mlkem768x25519-sha256` hybrid KEX (OpenSSH 10) | §3.1 + existing Curve25519 | | OpenSSH 10 client connects |
| 3.3 | NTRU Prime (sntrup761) | Poly arithmetic over Z/4591, hash-based KEM | | `sntrup761x25519-sha512@openssh.com` negotiates |

## 4 · SSH — Modern host keys / user auth

| # | Task | Acceptance |
|---|------|-----------|
| 4.1 | Ed448 host-key (`ssh-ed448`) — field + signing + blob | Test vector pass |
| 4.2 | OpenSSH certificate host keys `ssh-ed25519-cert-v01@openssh.com`, `rsa-sha2-*-cert-v01@openssh.com` | Client accepts CA-signed host cert |
| 4.3 | FIDO/SK public-key auth (`sk-ssh-ed25519@openssh.com`, `sk-ecdsa-sha2-nistp256@openssh.com`) — server-side verify | `ssh -i resident_key` authenticates |

---

## 5 · TLS — Ground up to 1.3, then PQ

The current code is TLS 1.2 only. Do 1.3 end-to-end before adding PQ so the
hybrid work has a home.

### 5.1 Primitives

| # | Task | New / touched file | Notes |
|---|------|--------------------|-------|
| 5.1.1 | SHA-3 / Keccak-f[1600] + SHAKE128/256 | `common/crypto/sha3.spl` | Needed by ML-KEM and modern HKDF uses |
| 5.1.2 | HKDF-Expand-Label / Derive-Secret (RFC 8446 §7.1) | `tls/key_schedule.spl` | |
| 5.1.3 | Ed25519 verify (have sign; verify needed for peer certs) | `common/crypto/ed25519.spl` | |
| 5.1.4 | RSASSA-PSS sign + verify | `common/crypto/rsa_pss.spl` | Required for `rsa_pss_rsae_sha256/384/512` sigalgs |
| 5.1.5 | ECDSA P-256 / P-384 verify | `common/crypto/ecdsa.spl` | P-256 partly there |
| 5.1.6 | X25519 raw (already exists as `rt_dh_curve25519_*`) — expose through `common/crypto/x25519.spl` without FFI for baremetal path | | |

### 5.2 TLS 1.3 core

| # | Task | File | Acceptance |
|---|------|------|-----------|
| 5.2.1 | Record layer: TLSInnerPlaintext, application_data, content_type after AEAD | `tls/record.spl` | Round-trip vs BoringSSL |
| 5.2.2 | Handshake state machine: ClientHello / HelloRetryRequest / ServerHello / EncryptedExtensions / Certificate / CertificateVerify / Finished | `tls/handshake.spl` | Full handshake to `curl` |
| 5.2.3 | Key schedule: early / handshake / master / resumption secrets | `tls/key_schedule.spl` | NIST/RFC test vectors |
| 5.2.4 | Suites: `TLS_AES_128_GCM_SHA256` (0x1301), `TLS_AES_256_GCM_SHA384` (0x1302), `TLS_CHACHA20_POLY1305_SHA256` (0x1303) | `tls/cipher.spl`, `tls/types.spl` | All three selectable |
| 5.2.5 | `supported_versions`, `key_share`, `signature_algorithms`, `signature_algorithms_cert` extensions | `tls/handshake.spl` | Real clients accept |
| 5.2.6 | ALPN (`h2`, `http/1.1`) + SNI parse/dispatch | `tls/handshake.spl` | Correct ALPN negotiated |

### 5.3 TLS 1.2 fill-ins (legacy path, still widely deployed)

| # | Task |
|---|------|
| 5.3.1 | `ECDHE_ECDSA_WITH_AES_128_GCM_SHA256` + `_AES_256_GCM_SHA384` + `_CHACHA20_POLY1305_SHA256` |
| 5.3.2 | RFC 7627 Extended Master Secret |
| 5.3.3 | RFC 7919 `ffdhe*` groups (optional; skip if time-constrained) |

### 5.4 Post-quantum

| # | Task | Acceptance |
|---|------|-----------|
| 5.4.1 | Reuse §3.1 ML-KEM-768 impl | |
| 5.4.2 | Hybrid named-group `X25519MLKEM768` (code 0x11EC) | Chrome connects over PQ |
| 5.4.3 | Optional: `X25519Kyber768Draft00` (0x6399) for older clients | |

### 5.5 X.509 + cert chain

| # | Task | File |
|---|------|------|
| 5.5.1 | DER parser hardening (length overflow, tag checks, indefinite-length reject) | `common/crypto/asn1.spl` (verify or create) |
| 5.5.2 | Path validation: name constraints, EKU, basic constraints, AIA | `tls/validation.spl` |
| 5.5.3 | OCSP stapling (status_request extension, verify response) | `tls/ocsp.spl` |
| 5.5.4 | SCT / Certificate Transparency verification (RFC 6962) | `tls/sct.spl` |

---

## 6 · Web-server / HTTPS wiring

| # | Task | File | Acceptance |
|---|------|------|-----------|
| 6.1 | Add `TlsListener.bind(addr, cert, key)` in front of `TcpListener` | `lib/nogc_sync_mut/tls/listener.spl` (new) | Test: self-signed cert, `curl --cacert` works |
| 6.2 | `HttpServer.start_tls(port, cert, key)` path in `lib/nogc_sync_mut/http_server` + `lib/nogc_async_mut/http_server` | mirrored in both | HTTP/1.1 over TLS serves static route |
| 6.3 | Switch `src/app/ui.web/server.spl` default to TLS when `--https` flag or cert files present; keep plaintext fallback with `--allow-http` | `ui.web/server.spl`, `ui.web/tls_serve_loop.spl` | Web UI loads on `https://localhost:PORT` |
| 6.4 | `wss://` — WebSocket over the TLS stream | `lib/nogc_sync_mut/websocket/tls_upgrade.spl` | Browser opens a `wss://` connection and receives live updates |
| 6.5 | HTTP/2 over ALPN `h2` (h2-over-TLS; HPACK, frame multiplexer) | `lib/nogc_sync_mut/http2/*.spl` (new) | `curl --http2` serves |
| 6.6 | HTTP/3 / QUIC — **defer**, file a feature request instead (very large scope; track only the capability gap) | — | Feature request filed in `doc/08_tracking/feature_request/` |

---

## 7 · Compiler / interpreter bug + perf hunt list

During each §1–§6 task, any new instance of the below is captured as a real
bug/feature-request with minimal repro; it is **not** worked around silently.

Already known (track here for convergence):

- **Cranelift `>>` broken on Rust bootstrap backend** — blocks naive SHA/AES
  bit-serial code paths. (memory: `feedback_cranelift_shr_bug.md`.) §7.1
- **Interpreter multi-MiB `[u8]` build slow** — kills crypto KAT suites and
  large packet tests. (memory: `feedback_interpreter_bulk_buffer.md`.) §7.2
- **Bitfield sugar missing** — driver framework C.3 follow-up; same sugar
  makes AES / SHA / GCM code 2–3× shorter. §7.3

Hunt-list (expect to hit during implementation; open a bug entry per instance):

- **u8 byte-copy loops** in SHA / AES / HMAC — measure interpreter vs compiled;
  if gap > 50×, propose `rt_bytes_copy_slice` intrinsic before hand-rolling.
- **`u32.to_be_bytes` / `u64.to_be_bytes`** usage — if not already folded,
  check whether the compiler turns them into 4/8-instruction BE stores or
  a function call.
- **Constant-time compare** — confirm the optimizer does not rewrite
  XOR-accumulate compares into short-circuit branches. If it does, add a
  `@no_branch_fold` / `black_box()` attribute (feature request if missing).
- **AES T-tables (256-entry `const [u32;256]`)** — make sure const init does
  not regenerate at runtime; if it does, file a const-folding bug.
- **GF(2^128) mul for GCM** — 128-bit shift/xor micro-benchmark; consider
  `carryless_mul` intrinsic feature request if 10× slower than target.
- **Curve25519 26-bit-limb field ops** — measure `u64.mul_hi` codegen; if
  the compiler emits a library call, file a codegen improvement.
- **Big-integer RSA / ML-KEM NTT** — watch for quadratic behaviour in
  `[u64].push`; if found, propose a `Vec::with_capacity` equivalent.
- **`match` on algorithm ID numeric constants** — if the compiler falls
  through to an if/elif chain rather than a jump table, file a codegen
  improvement with a 16-arm test case.
- **SSpec `--mode=smf` / `--compile` wrapper** — already flagged in memory
  (`feedback_sspec_compile_pipeline.md`); re-verify after each crypto module
  lands, since it directly blocks release-mode crypto tests.
- **`extern fn` additions → bootstrap rebuild** — if a new `rt_*` is added
  in §5 or §6, follow the deploy flow from `feedback_extern_bootstrap_rebuild.md`
  (`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`), not `bin/simple build`.

Place each new bug in `doc/08_tracking/bug/bug_report.md` with a one-line link
back to the §-task that uncovered it.

---

## 8 · Sequencing

```
§1.1 §1.2 §1.3  ──┐
                  ├──►  §2.1 §2.2  ──►  §4.x (can run in parallel with §5)
§1.4 §1.5 ────────┘

§5.1 (primitives) ──► §5.2 (TLS 1.3 core) ──► §5.2.4..6
                                        └──►  §6.1..6.3 (HTTPS wiring)
                                                       └──►  §6.4 wss  ──►  §6.5 h2
§5.1.1 ──► §3.1 (ML-KEM) ──► §3.2 §3.3 (SSH PQ) ──► §5.4 (TLS PQ)
```

Ship criteria per milestone:

- **M1:** §1 done — modern SSH advertisement matches OpenSSH 9 defaults.
- **M2:** §2 + §4.2 — ETM MACs + certificate host keys.
- **M3:** §5.1 + §5.2 — TLS 1.3 end-to-end with real browser.
- **M4:** §6.1..§6.4 — HTTPS web UI on `https://` + `wss://`.
- **M5:** §3 + §5.4 — PQ KEX on both SSH and TLS.
- **M6:** §6.5 — HTTP/2. (HTTP/3 / QUIC remains as tracked gap, not a task.)

---

## 9 · Testing

- **KAT / RFC test vectors** under `test/crypto/kat/` for every primitive
  (SHA-3, HKDF-Expand-Label, ML-KEM, RSASSA-PSS, ECDSA verify).
- **Interop smoke tests** against real stacks (`ssh` OpenSSH 9/10, `openssl
  s_client`, `curl --tlsv1.3`, Firefox/Chrome if UI is wired) under
  `test/integration/`.
- **Negotiation unit tests** asserting each algorithm name is *advertised*,
  *selectable*, and *rejected* when the peer does not offer it.
- **Regression**: run `bin/simple build check` after each milestone; if a
  perf regression shows up, either fix or file (per CLAUDE.md rule).
