# Crypto Recovery Status

Date: 2026-04-26
Branch policy: use `main` as the consolidation line.

## Milestone State

- M1 SSH baseline: complete.
  Focused SSH transport/session gates are green, `ecdsa-sha2-nistp256` is live, strict-kex is present, and `EXT_INFO` support is wired.
- M2 SSH transport + host certificates: implemented in this pass, with one canary still outside the release gate.
  `aes256-ctr` plus `hmac-sha2-256-etm@openssh.com` and `hmac-sha2-512-etm@openssh.com` are now advertised and enforced in negotiation.
  CTR+ETM packet framing helpers were added and covered by unit tests.
  Loader support for OpenSSH host-certificate public blobs is present for `ssh-ed25519-cert-v01@openssh.com`, `rsa-sha2-256-cert-v01@openssh.com`, and `rsa-sha2-512-cert-v01@openssh.com`.
  Session-side host-key blob selection now accepts certificate algorithms.
  The legacy `test/unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` canary is still red due pre-existing helper drift (`.to_bytes()` and `rt_bytes_u8_at` usage) and is not used as a release gate.
- M3 TLS 1.3 completion: in progress.
  The current stack under `src/os/tls13/` is real and has active hosted and baremetal test coverage again, but broader TLS 1.3 interop and validation gaps still remain before M3 can be called complete.
- M4 HTTPS + `wss://`: in progress.
  The browser-side generated WebSocket clients now derive `ws` vs `wss` from `location.protocol`, and the host web server no longer hides the TLS serve loop behind `UI_WEB_V2` when `--tls`/`--https` is requested.
  Full milestone completion is still blocked on broader TLS M3 live interop and on deciding whether to keep the existing rustls-backed `TlsWebServer` backend or replace it with a server-side `src/os/tls13` implementation later.
- M5 PQ SSH/TLS extensions: not started in this pass.
- M6 HTTP/2 over HTTPS: not started in this pass.

## SSH M2 Verification

Green in this pass:

- `test/unit/os/apps/sshd/ssh_transport_spec.spl`
- `test/unit/os/apps/sshd/ssh_packet_spec.spl`
- `test/unit/os/apps/sshd/ssh_session_hostkey_blob_spec.spl`
- `test/unit/os/apps/sshd/sshd_spec.spl`
- `test/system/os_ssh_host_key_loader_spec.spl`

Canary only, still red:

- `test/unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl`

## TLS M3 Audit Findings

- TLS 1.3 client negotiation is still narrow: X25519-only groups, Ed25519-only advertised signature algorithms, and `TLS_AES_128_GCM_SHA256` only.
- `CertificateVerify` handling covers Ed25519 and RSA-PSS, but not TLS-side ECDSA verification.
- `EncryptedExtensions` parsing is effectively stubbed and not validating ALPN or related extension semantics.
- `ServerHello` handling does not implement HelloRetryRequest or broader TLS 1.3 extension/state validation.
- Current hosted interop proves handshake mechanics more than full certificate-validation breadth, and current fixtures are Ed25519-centric.

## TLS Progress In This Pass

- Fixed the missing server `CertificateVerify` content builder in `src/os/tls13/tls13.spl`.
- Removed `src/os/tls13/handshake13.spl` reliance on runtime-only `rt_bytes_u8_at` / `rt_array_new_with_cap` for the pure helper paths used by TLS client-auth tests.
- Aligned the shared hosted TLS fixture config defaults and checked-in `tools/tls_test_server/server.sdn` to `build/tls_test_server`.
- Fixed the immediate `examples/simple_os/arch/x86_64/boot/ed25519_verify_helper.c` compile errors caused by missing `NIL_VALUE` / `_crypto_make_byte_array`.
- Routed the TLS baremetal entries through the existing freestanding-stub test harness path in `src/os/qemu_runner.spl`, restoring `os_tls_spec` and `os_tls_system_spec` builds without changing the production OS entry policy.
- Removed unnecessary explicit TLS type imports and local type annotations from `examples/simple_os/arch/x86_64/tls_unit_entry.spl` so the test kernel no longer emits entry-local unresolved type symbols.
- Removed the generic byte-array extern dependency from the hosted TLS core in `src/os/tls13/{tls13,record13}.spl`, and from the pure AES-GCM helper in `src/os/crypto/aes128_gcm.spl`, replacing those uses with local Simple helpers where possible.
- Added `rt_array_new_with_cap` to the Rust runtime/compiler symbol inventories for native lanes.
- Fixed the interpreter-side Ed25519 verifier dispatch to match the Simple calling convention `(message, pubkey, signature)` and wired `rt_tls13_ed25519_verify` to the same interpreter handler for hosted TLS verification.
- Audited the live TLS acceptance lanes: hosted basic interop is green, but hosted mTLS still fails during client `Finished` send, and both QEMU live lanes remain red when `SIMPLEOS_QEMU_TLS_LIVE=1` / `SIMPLEOS_QEMU_TLS_SYSTEM_LIVE=1` are actually enabled.
- Confirmed there is still no exact `openssl s_client -tls1_3` or `curl --tlsv1.3` release lane in-tree; current OpenSSL helper coverage is hosted and not TLS-1.3-pinned.

## HTTPS / WSS Progress In This Pass

- `src/app/ui.web/html.spl` now generates protocol-aware browser clients for both `/ws` and `/ui/ws`, using `wss://` automatically when the page is loaded over HTTPS while keeping the explicit port as a fallback for local generation tests.
- `src/app/ui.web/server.spl` now treats `--tls` and `--https` as the normal HTTPS startup path and routes both through `serve_tls(...)` directly instead of falling back to the plain async server when `UI_WEB_V2` is unset.
- Focused browser-generation gates are green:
  - `test/unit/app/ui/wm_html_spec.spl`
  - `test/system/gui/web_api_spec.spl`
- `test/system/gui/native_gui_build_spec.spl` remains red, but on pre-existing spec issues (`type mismatch: comparing string with integer`) unrelated to the new HTTPS/`wss://` wiring.

Green after these fixes:

- `test/system/os_tls_client_auth_spec.spl`
- `test/system/os_tls_hosted_interop_basic_spec.spl`
- `test/system/os_tls_spec.spl`
- `test/system/os_tls_system_spec.spl`
- Hosted Simple client probe is now green under `simple run`, not just the OpenSSL fixture validation half of the spec.

**HRR support landed 2026-05-01** — see `src/os/tls13/handshake13.spl` and `test/unit/os/tls13/hello_retry_request_spec.spl`.

## Next Execution Order

1. Repair the TLS M3 live gaps on the existing `src/os/tls13` stack, starting with hosted mTLS and the env-gated QEMU live failures.
2. Add exact `openssl s_client -tls1_3`, `openssl s_server -tls1_3`, and `curl --tlsv1.3` coverage on top of the now-green default hosted gates.
3. Finish M4 by validating the HTTPS startup path end-to-end with browser/`wss://` smokes and deciding whether the existing rustls-backed `TlsWebServer` remains the production server backend.
4. Defer M5 PQ and M6 HTTP/2 until M3 and M4 are green.

## Status Update (2026-05-01)

KAT vector specs landed since 2026-04-26:

- SHA-256 + SHA-512 NIST FIPS 180-4 reference vectors.
- AES-256-GCM NIST CAVS RFC vectors.
- ChaCha20-Poly1305 RFC 8439 reference + known-answer vectors.
- HMAC-SHA-256 + HMAC-SHA-512 RFC 4231 vectors.
- Curve25519 RFC 7748 reference vectors.
- RSA-SHA-256 PKCS#1 v1.5 round-trip.
- ECDSA-P256-SHA-256 (14 vectors, paths B+C+D).
- Poly1305 RFC 8439 §2.5.2 + §A.3 standalone vectors.
- AES-CTR NIST SP 800-38A reference vectors.
- HKDF RFC 5869 (Extract+Expand) for SHA-256 and SHA-512.

Open blockers:

- bug `aes128_gcm_stub_2026-05-01.md` — 4 externs (`rt_aes_sbox`, `rt_aes_rcon`, `rt_aes128_encrypt_block_into`, `rt_tls13_aes128_gcm_encrypt`) are unregistered; AES-128-GCM NIST KAT cannot run in interpreter (separate sstack agent fixing this).
- bug `crypto/Ed25519 RFC 8032 §7.1 byte-mismatch` (per recent commit doc).
- bug `jwt/HS256 round-trip failure` (RFC byte-match passes, sign+verify fails).

Open feature requests:

- FR `pqc/hybrid KEX design (X25519MLKEM768 + sntrup761x25519)` — design filed.
- FR `simd_int_intrinsics_for_crypto_2026-05-01` Phase 1 IN PROGRESS — will unblock vectorized ChaCha20+SHA in pure Simple.

TLS 1.3 / M3 narrow-surface gaps (still): no ECDSA TLS-side verification, EncryptedExtensions stub, no HelloRetryRequest, only `TLS_AES_128_GCM_SHA256` cipher suite advertised.

## Wave 1 Outcomes (2026-05-01 evening)

> This section supersedes the "Open blockers" / "TLS 1.3 / M3 narrow-surface gaps" lines above where they conflict — Wave 1 closed several of them. Wave 2 is in flight at time of writing.

### TLS M3 progress

- **EncryptedExtensions parser — LANDED** (Agent H): full RFC 8446 §4.3.1 parse with ALPN + supported-version enforcement; 11/11 specs PASS.
- **HelloRetryRequest detection + ClientHello2 + synthetic message_hash — LANDED** (Agent I): RFC 8446 §4.1.4 + §4.4.1; 17/17 specs PASS in `test/unit/os/tls13/hello_retry_request_spec.spl`. Connect-flow integration of HRR is **DEFERRED until a 2nd NamedGroup lands** (P-256 candidate) — HRR has no second group to retry with on the wire today.
- **TLS-side ECDSA-P256 CertificateVerify — already supported** (audit correction): the M3 audit findings list ECDSA TLS-side verify as "missing"; that line is stale. `cert_verify` already accepts ECDSA-P256. The narrow-surface gap is the ClientHello *advertisement* set, not the verifier.

### Crypto primitive fixes

- **Ed25519 RFC 8032 §7.1 byte-mismatch — FIXED** (Agent G): 15/15 vectors PASS. Root cause was unwired baremetal externs, not the crypto math. Constant-time scalar_mul follow-up filed at `doc/08_tracking/bug/ed25519_scalar_mul_not_constant_time_2026-05-01.md` (OPEN; Wave 2 T4 in flight).
- **JWT HS256 round-trip — FIXED at root cause by Agent Q at `4daecc081b`**: the failure was an interpreter caller bug (`text.from_char_code(n)` is not a supported text method); rewritten to `n.chr()` across 9 call sites in jwt/encode, cert/pem, and http/utilities. Underlying interpreter bug filed at `doc/08_tracking/bug/interpreter_match_ok_arm_text_type_lookup_2026-05-01.md` and FIXED in the same change. **REQ-JWT-005 PASS**. **REQ-JWT-006 still fails** for a separate helper-fn-return-from-match limitation in the interpreter (Wave 2 T8 diagnosing).
- **AES-128-GCM externs — LANDED** (Agent B): `rt_aes_sbox`, `rt_aes_rcon`, `rt_aes128_encrypt_block_into`, `rt_tls13_aes128_gcm_encrypt` registered + dispatched. 4/4 NIST SP 800-38D Appendix B encrypt vectors byte-exact PASS. **Decrypt FAILs on 8 vectors** — pre-existing bug filed at `doc/08_tracking/bug/aes128_gcm_decrypt_string_to_int_2026-05-01.md` (OPEN; Wave 2 T3 fixing).
- **PBKDF2 HMAC-SHA-256 perf — 2.3× speedup** (Agent P): hoisted tail-block templates + cached K_ipad/K_opad SHA-256 prefix states; `c=4096` now 78s (was 180s). This is the pure-Simple ceiling; FR `doc/08_tracking/feature_request/pbkdf2_native_runtime_helpers_2026-05-01.md` filed for native helpers targeting ~1s.

### Open blockers post-Wave-1

- `aes128_gcm_decrypt_string_to_int_2026-05-01` — Wave 2 T3 fixing now.
- `ed25519_scalar_mul_not_constant_time_2026-05-01` — Wave 2 T4 fixing now.
- `hmac_sha512_pbkdf2_mismatch_2026-05-01` — RFC 7914 vector mismatch on HMAC-SHA-512 PBKDF2; no fix yet (filed by P).
- REQ-JWT-006 helper-fn-return-from-match interpreter limitation — Wave 2 T8 diagnosing.
- Zstd FSE Huffman-weight Kraft completion (`bug_zstd_fse_huffman_weight_kraft_2026-05-01`) — multi-day; not crypto but blocks compression M3 closure.

### Wave 1 FR filings

- `doc/08_tracking/feature_request/lzma2_full_lclppb_2026-05-01.md` — LCLPPB tuples beyond 3/0/2 (compression).
- `doc/08_tracking/feature_request/pbkdf2_native_runtime_helpers_2026-05-01.md` — native HMAC inner-loop helpers for PBKDF2.
- `doc/08_tracking/feature_request/static_file_compression_cache_integration_2026-05-01.md` — **LANDED** in Wave 1 by Agent C.
- `doc/08_tracking/feature_request/simd_int_intrinsics_for_crypto_2026-05-01.md` — Phase 1 (10 int intrinsics) **LANDED**; Phase 2 (`Vec16u8` + AES-NI) and Phase 3 (`Vec2u64` + PCLMUL) **OPEN**.
