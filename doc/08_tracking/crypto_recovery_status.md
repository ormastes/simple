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

**HRR connect-flow integration LANDED 2026-05-01** — closes I-Wave1's deferred AC. M3 milestone advances. `tls13_connect_io_with_config` now detects HRR via `is_hello_retry_request(sh)` after `parse_server_hello`, calls the new pure helper `process_hrr_after_serverhello` (in `src/os/tls13/handshake13.spl`) which enforces RFC 8446 §4.1.4 rejections (only one HRR per handshake; HRR must change group; selected_group must be one the client advertised) and produces the §4.4.1 transcript seed `synthetic_message_hash || HRR-handshake-bytes`. CH2 is routed to `build_client_hello2_bytes_with_p256` for `GROUP_SECP256R1` and `build_client_hello2_bytes` for `GROUP_X25519` (latter currently unreachable from live connect because CH1 advertises X25519 → same-group rejection; retained for future). Deferred per AC-7: full P-256 ECDHE shared-secret derivation + key_schedule integration after CH2 send — connect returns `Failed("HRR P-256 ECDHE deferred — see crypto_recovery_status.md M3")` until that lands. Spec coverage: 9/9 PASS in `test/unit/os/tls13/hrr_connect_flow_spec.spl` (interpreter mode).

## Wave 6 (2026-05-01) — P-256 ECDHE → handshake_secret integration

**P-256 ECDHE → handshake_secret integration LANDED 2026-05-01 — closes W5-A AC-7.** The HRR-after-CH2 connect-flow no longer returns `Failed("HRR P-256 ECDHE deferred ...")`. On the `GROUP_SECP256R1` branch in `src/os/tls13/tls13.spl` (commit `41a14b193e`, bundled into a parallel-agent wip-checkpoint per `.claude/memory/feedback_wip_snapshot_half_ship.md`), the client now:

1. Sends CH2 with the fresh P-256 ephemeral.
2. Replaces the transcript with the §4.4.1 seed (`synthetic_message_hash || HRR-handshake-bytes || CH2`) and receives SH2.
3. Validates SH2 cipher_suite is 0x1301 (`TLS_AES_128_GCM_SHA256`); SHA-384 (0x1302) is a follow-up.
4. Parses SH2's key_share extension via the new `_serverhello_p256_pub` helper (RFC 8446 §4.2.8.2 + RFC 8422 §5.4: 65-byte uncompressed `04 || X || Y`). `ServerHello13` gained a `p256_pub: [u8]` field alongside `x25519_pub`.
5. Computes `p256_ecdh_shared_x(client_priv, server_p256_pub)` → 32-byte shared X.
6. Calls `tls13_compute_handshake_secrets(p256_shared, transcript)` to derive `handshake_secret` + client/server handshake-traffic secrets.
7. Calls `tls13_traffic_keys` for both directions (16-byte AES-128 key + 12-byte IV per direction).

Deferred (AC-5, surfaced as a new typed `Failed` reason `"HRR P-256 handshake-secret derived; Finished MAC verify deferred — see crypto_recovery_status.md Wave 6"`): server Finished MAC verify, client Finished, application traffic secrets / app traffic keys.

**Constant-time threshold note.** Wave 6 is the first caller that exposes the P-256 ephemeral private key through the handshake_secret schedule. The CT scalar-mult hardening landed in parallel (`5b1abf1ea6 fix(p256): constant-time scalar multiplication on secret path`) closes change #1 of `doc/08_tracking/feature_request/p256_scalar_mult_constant_time_2026-05-01.md`. Items #2/#3 (`_jac_add_mixed` equal-points / `_jac_double` inf branches) remain tracked under that FR and SHOULD land before broad ECDHE exposure.

**Spec coverage:**
- `test/unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl`: AC-1 + AC-2 = 5/5 PASS (P-256 keypair shape + ECDHE shared-X symmetry `client*server == server*client`). AC-3 + AC-4 (handshake_secret + traffic_keys round-trip) are blocked by two parallel-agent regressions documented in `doc/08_tracking/bug/p256_keypair_pub_fn_arg_u64_index_regression_2026-05-01.md`: (a) `semantic: cannot index array with type \`u64\`` when a fn-return `[u8]` reaches `p256_keypair_pub`, (b) `rt_tls13_hkdf_extract_into` extern declared but not wired in the runtime. Inline-scalar workaround in AC-1+AC-2 keeps coverage real (no skip / no weakened assertions per `feedback_no_coverups.md`).

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
- **P-256 NamedGroup advertise + keypair gen LANDED 2026-05-01** — connect-flow integration + ECDHE deferred. `secp256r1` (0x0017) is now in `supported_groups` and a P-256 KeyShareEntry can ride alongside the X25519 entry in `key_share`. 13/13 specs PASS in `test/unit/os/tls13/p256_named_group_spec.spl`. Pure-Simple Jacobian scalar-mult (`src/os/crypto/ecdh_p256.spl`) verified by `k=1 ⇒ G` byte-equality against the SEC2 generator. Deferred follow-ups: server-side P-256 key_share consumption, ECDHE shared-secret derivation, handshake_secret integration, HRR connect-flow wiring (now unblocked). Constant-time hardening of P-256 scalar-mult MUST land before any caller exposes the ephemeral private key through the handshake_secret schedule.
- **TLS-side ECDSA-P256 CertificateVerify — already supported** (audit correction): the M3 audit findings list ECDSA TLS-side verify as "missing"; that line is stale. `cert_verify` already accepts ECDSA-P256. The narrow-surface gap is the ClientHello *advertisement* set, not the verifier.

### Crypto primitive fixes

- **Ed25519 RFC 8032 §7.1 byte-mismatch — FIXED** (Agent G): 15/15 vectors PASS. Root cause was unwired baremetal externs, not the crypto math. Constant-time scalar_mul follow-up filed at `doc/08_tracking/bug/ed25519_scalar_mul_not_constant_time_2026-05-01.md` (OPEN; Wave 2 T4 in flight).
- **JWT HS256 round-trip — FIXED at root cause by Agent Q at `4daecc081b`**: the failure was an interpreter caller bug (`text.from_char_code(n)` is not a supported text method); rewritten to `n.chr()` across 9 call sites in jwt/encode, cert/pem, and http/utilities. Underlying interpreter bug filed at `doc/08_tracking/bug/interpreter_match_ok_arm_text_type_lookup_2026-05-01.md` and FIXED in the same change. **REQ-JWT-005 PASS**. **REQ-JWT-006 still fails** for a separate helper-fn-return-from-match limitation in the interpreter (Wave 2 T8 diagnosing).
- **AES-128-GCM externs — LANDED** (Agent B): `rt_aes_sbox`, `rt_aes_rcon`, `rt_aes128_encrypt_block_into`, `rt_tls13_aes128_gcm_encrypt` registered + dispatched. 4/4 NIST SP 800-38D Appendix B encrypt vectors byte-exact PASS. **Decrypt FAILs on 8 vectors** — pre-existing bug filed at `doc/08_tracking/bug/aes128_gcm_decrypt_string_to_int_2026-05-01.md` (OPEN; Wave 2 T3 fixing).
- **TLS_AES_256_GCM_SHA384 (0x1302) cipher suite LANDED 2026-05-01** — AES-256 + SHA-384 + HKDF-SHA-384 wired (Wave 4). Runtime: `expand_key_aes256` + `aes256_gcm_encrypt_bytes` + `rt_tls13_aes256_gcm_encrypt` + `rt_aes256_encrypt_block_into` (5/5 Rust unit tests TC13–TC16 + FIPS 197 §C.3 PASS byte-exact in `src/compiler_rust/runtime/src/value/aes.rs`). Caller: pure-Simple `src/os/crypto/aes256_gcm.spl` mirroring AES-128 structure. Wire: ClientHello cipher_suites now advertises `{0x1301, 0x1302}` per RFC 8446 §9.1 with cipher_suites_len bumped 0x0002→0x0004. Key schedule: SHA-384 sibling functions (`tls13_early_secret_sha384`, `tls13_handshake_secret_sha384`, `tls13_master_secret_sha384`, `tls13_traffic_keys_sha384`, `tls13_finished_key_sha384`, `tls13_verify_data_sha384`) in `src/os/tls13/key_schedule.spl` + `hkdf_extract_sha384` / `hkdf_expand_label_sha384` in `src/os/tls13/hkdf.spl` (powered by `std.crypto.hmac.hmac_sha384_bytes`). Specs: `test/unit/lib/crypto/aes256_gcm_nist_vectors_spec.spl` (encrypt 4/4 + corruption-rejection 4/4 PASS; round-trip decrypt 4 fail — same interpreter Arc-clone pattern as AES-128) and `test/unit/os/tls13/aes256_gcm_sha384_cipher_suite_spec.spl` (8/10 PASS; advertise + AEAD encrypt + SHA-384 key_schedule fully verified). **DEFERRED** (AC-9): server-side negotiation fixture + rustls/openssl interop.
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

## Wave 4 In Flight (2026-05-01 evening)

- **T20** — backfill missing interpreter dispatch arms for `rt_simd_{add,sub,mul}_i32x{4,8}`. T1 (Wave 3) surfaced these as declared-extern-but-undispatched during ChaCha20 vectorization; downstream consumers currently trap when the FFI table is hit directly.
- **T21** — implement `TLS_AES_256_GCM_SHA384` (cipher suite 0x1302). Closes the M3 narrow-surface gap "only `TLS_AES_128_GCM_SHA256` cipher suite advertised" carried over from Wave 1.
- **T24** — Zstd dict-frame end-to-end test that round-trips a host `zstd --train --dict` payload. If green, flips `verify_common_compression_framework.md`'s `zstd.spl:1265` line from WARN to PASS (status would become `FAIL (5 failures, 4 warnings)`).
- **T25** (this entry, doc-only) — Wave 1–3 cleanup sweep + history disambiguation. Audit landed at `doc/09_report/verify/wave_1to3_audit_2026-05-01.md`; verify report status counts re-verified; SIMD plan annotated with Phase 1 dispatch gap.

### Wave 4+ deferred

- HRR connect-flow integration is **UNBLOCKED** by Wave 3 T7's P-256 NamedGroup advertise + ephemeral keypair gen (`xqxspqnmyyqk`, `vovnmzmknppp`, `onllvytpzmkt`, `voqupwqqwzxt`). Wiring HRR through `tls13_client_connect` was not owned by any in-flight Wave 4 agent; defer to Wave 5 / future session.
- P-256 scalar multiplication is **not constant-time** on the secret path; FR `p256_scalar_mult_constant_time_2026-05-01` filed; no Wave 4 owner.

## Wave 5 Outcomes (2026-05-01 evening)

- **TLS_CHACHA20_POLY1305_SHA256 (0x1303) cipher suite LANDED 2026-05-01** — third TLS 1.3 mandatory cipher suite per RFC 8446 §9.1 now advertised + record-layer wired. Pure-Simple end-to-end: ChaCha20 (with T1's SIMD speedup, 1.7-1.8×) + Poly1305 + RFC 8439 AEAD wrapper + SHA-256 + HKDF-SHA-256 already in tree; this wave only added the cipher-suite advertise + record-layer dispatch + key-schedule traffic-key sibling. **No new Rust extern.** Wire: ClientHello cipher_suites now advertises `{0x1301, 0x1302, 0x1303}` per RFC 8446 §9.1 with `cipher_suites_len` bumped 0x0004→0x0006. Dispatch: `record13_encrypt_chacha20_poly1305` + `record13_decrypt_chacha20_poly1305` + `record13_encrypt_for_suite(suite, ...)` + `record13_decrypt_for_suite(suite, ...)` in `src/os/tls13/record13.spl` route to the new path when `0x1303` is negotiated and fall back to the existing AES-128-GCM path otherwise. Per-record nonce derived per RFC 8446 §5.3 via the existing `record13_make_nonce` (IV XOR seq_num, right-aligned big-endian). Key schedule: `tls13_traffic_keys_chacha20(traffic_secret) -> TrafficKeys` (32B ChaCha20 key + 12B IV) added to `src/os/tls13/key_schedule.spl`; existing SHA-256 helpers (`tls13_early_secret`, `tls13_handshake_secret`, `tls13_master_secret`, `tls13_finished_key`, `tls13_verify_data`) reused unchanged per RFC 8446 §B.4 (SHA-256 shared with `TLS_AES_128_GCM_SHA256`). Specs: `test/unit/os/tls13/chacha20_poly1305_cipher_suite_spec.spl` 14/14 PASS in interpreter mode (`bin/simple <spec>` direct, per `feedback_compile_mode_false_greens.md`) — covers constant value, advertise byte-format, AEAD encrypt + round-trip + tag-corruption rejection, RFC 8446 §5.3 nonce derivation (seq_num=0 vs seq_num=1), record-layer round-trip with both seq_num values, mismatched-seq_num rejection, and `record13_encrypt_for_suite` dispatch identity. **DEFERRED**: `tls13_traffic_keys_chacha20` shape-test + SHA-256 handshake_secret regression — both transitively invoke `rt_tls13_hkdf_*` runtime externs unresolved in interpreter mode (same pattern as T21's AES-256-GCM decrypt path); covered by compiled-mode runs. Full server-side negotiation fixture + rustls/openssl interop also deferred. Closes the last "narrow-surface cipher suite" line item from Wave 1.

## Wave 9 (2026-05-02) — M5 PQ seed: ML-KEM-768 (FIPS 203) pure-Simple landing

**M5 PQ — ML-KEM-768 seeded; ready for hybrid TLS 1.3 wiring next wave.**

Wave 9 lands the pure-Simple foundation for post-quantum key encapsulation
per NIST FIPS 203 (Module-Lattice-Based Key-Encapsulation Mechanism Standard,
August 2024). This unblocks TLS 1.3 hybrid key exchange (X25519 + ML-KEM-768)
per draft-ietf-tls-hybrid-design in a future wave.

Files added:

- `src/os/crypto/ml_kem_ntt.spl` — Z_q polynomial arithmetic over q=3329, NTT
  with primitive 256th root ζ=17, INTT with the 128⁻¹ scale (3303),
  pointwise multiply in NTT domain, Compress_d / Decompress_d (Algorithm
  4 / 5), ByteEncode_d / ByteDecode_d (Algorithm 6 / 7). The zeta and
  gamma tables were Python-cross-checked before commit. (Landed in the
  parallel-agent wip-snapshot `ffbb6597cf` per
  `feedback_wip_snapshot_half_ship.md`; committed without a subject due
  to the auto-snapshot hook firing during edits.)
- `src/os/crypto/ml_kem_kpke.spl` — SHAKE-128 (rate=168) and SHAKE-256
  (rate=136) wrappers built on the shared `keccak_f1600` from
  `lib/common/crypto/sha3.spl` with FIPS 202 §B.2 domain byte 0x1F;
  G/H/J helpers; SamplePolyCBD η=2 (Algorithm 8); SampleNTT rejection
  sampling for Â (Algorithm 7); PRF_eta = SHAKE-256(s||b, 64·eta)
  (Algorithm 11); K-PKE.KeyGen / Encrypt / Decrypt (Algorithms 13/14/15)
  for k=3, eta1=eta2=2, du=10, dv=4. Sizes: ekPKE=1184B, dkPKE=1152B,
  c=1088B.
- `src/os/crypto/ml_kem.spl` — IND-CCA wrapper. ML-KEM.KeyGen wraps
  K-PKE.KeyGen and emits dk = dk_pke || ek || H(ek) || z (2400B).
  ML-KEM.Encaps derives (K, r) = G(m || H(ek)) and emits c = K-PKE.Encrypt
  (Algorithm 17). ML-KEM.Decaps runs the FO transform with **constant-time**
  selection between K′ and the implicit-rejection key J(z || c) via
  `_ct_bytes_eq` + `_ct_select_bytes` (no data-dependent branch on the
  ciphertext-equality check; per `feedback_no_coverups.md` and the
  ed25519 / p256 CT precedent).
- `test/unit/lib/crypto/ml_kem_768_kat_spec.spl` — pure-Simple property
  spec covering q sanity, FIPS 203 §4.2.1 Compress_1 boundary points
  (832 → 0, 833 → 1, 2496 → 1, 2497 → 0), ByteEncode/Decode round-trip
  shape, NTT round-trip shape, NTT pointwise multiply produces a
  well-formed 256-coefficient result, ML-KEM-768 size invariants
  (ek=1184, dk=2400, c=1088, K=32), and FIPS 202 SHAKE-128('') first
  16 bytes byte-exact match
  (`7F 9C 2B A4 E8 8F 82 7D 61 60 45 50 76 05 85 3E`).

End-to-end correctness was verified during development in module-level
top-level harnesses (interpreter mode, real execution rather than
load-only spec PASS):

- NTT round-trip on 256 coefficients (`ntt(p) → intt → p`): exact match.
- NTT pointwise multiply matches Python schoolbook reference exactly
  (a=3·k, b=5·k+1; c[0]=1621, c[1]=1901, c[255]=1471).
- K-PKE.Decrypt(dk_pke, K-PKE.Encrypt(ek_pke, m, r)) recovers m exactly,
  ~6 s end-to-end.
- ML-KEM.Decaps(dk, c) produces the same K as ML-KEM.Encaps for
  matching ciphertext, and a *different* K (via J(z || c)) when one
  ciphertext bit is flipped, ~13 s end-to-end.

Out of scope (Wave 10+): hybrid X25519+ML-KEM-768 TLS 1.3 wiring,
ML-KEM-512, ML-KEM-1024, ML-DSA (signatures), SLH-DSA (hash-based
signatures), NIST CCTV KAT vector injection (1184 B+ ek and 2400 B+ dk
fixtures need a bytes-from-file helper).

## Wave 7-8 Closure (2026-05-02) — TLS 1.3 HKDF runtime externs deployed via bootstrap rebuild

**W6-C / W7-B byte-exact path UNBLOCKED.**

`rt_tls13_sha256` and the full `rt_tls13_hkdf_*` family
(`rt_tls13_hkdf_extract`, `rt_tls13_hkdf_extract_into`,
`rt_tls13_hkdf_expand_into`, `rt_tls13_hkdf_expand_label`,
`rt_tls13_hkdf_expand_label_into`, `rt_tls13_hkdf_expand_label_derived`,
`rt_tls13_hkdf_expand_label_key`, `rt_tls13_hkdf_expand_label_iv`,
`rt_tls13_hkdf_expand_label_finished`,
`rt_tls13_hkdf_expand_label_client_hs`,
`rt_tls13_hkdf_expand_label_server_hs`,
`rt_tls13_hkdf_expand_label_client_app`,
`rt_tls13_hkdf_expand_label_server_app`) are registered in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:461-474`
referencing the `tls13::*` module at
`src/compiler_rust/compiler/src/interpreter_extern/tls13.rs`. These
entries had been added during W6-C source work but were not present in
the deployed `bin/simple` runtime, so W6-C/W7-B specs failed with
`unknown extern function: rt_tls13_hkdf_extract_into` per
`feedback_extern_bootstrap_rebuild.md`.

Resolution: ran `bash scripts/bootstrap/bootstrap-from-scratch.sh
--deploy`. Stages 2 and 3 self-host verification passed (stage2 sha256
== stage3 sha256
`e14ed1c7bb5a49ce7dd45bc38fa61ee29b28d1566e2353b148518aa3f11f1f67`).
Stage 4 full-CLI compile failed with 67 pre-existing
`hir: Cannot infer field type` errors in unrelated parallel-agent
edits (compiler/types/type_infer/, app/cli/, lib/common/crypto/sha256.spl,
lib/nogc_sync_mut/path.spl, etc.) — not regressions from this wave.
The bootstrap-staged seed binary at
`src/compiler_rust/target/bootstrap/simple` (which `bin/simple` wraps)
was rebuilt with the new extern table prior to the Stage 4 failure, so
the interpreter-driven TLS 1.3 path is unblocked.

Verification (`test/unit/os/tls13/`, interpreter mode per
`feedback_compile_mode_false_greens.md`):

- 12 spec files / 136 PASS / 3 FAIL
- 0 `unknown extern function` errors anywhere in the run (was the
  blocking signature for W6-C / W7-B)
- `p256_ecdhe_handshake_secret_spec.spl` — 11/11 PASS (was failing
  pre-rebuild with `unknown extern function: rt_tls13_hkdf_extract_into`)
- Remaining 3 failures all in `aes256_gcm_sha384_cipher_suite_spec.spl`
  (W8-3 `aes256_gcm.spl` work-in-progress AES path; unrelated to HKDF
  externs)

This closes the W6-C / W7-B byte-exact-handshake-secret blocker.
Stage 4 full-CLI compile failure is owned by other in-flight tracks and
is independent of TLS 1.3.

## Wave 10 (2026-05-02) — M5 PQ Signatures: ML-DSA-65 seed

- **ML-DSA-65 (FIPS 204) seeded** by Wave 10 W10-A as the post-quantum
  signature counterpart to W9-A's ML-KEM-768 (FIPS 203).  Files:
  `src/os/crypto/ml_dsa_ntt.spl` (413 lines — Algorithms 35-40 + NTT with
  q=8380417, ζ=1753 BitRev8 — distinct from ML-KEM's q=3329 / ζ=17 /
  BitRev7), `src/os/crypto/ml_dsa_sample.spl` (518 lines — local
  SHAKE-128/256 XOFs over the public `keccak_f1600` permutation since
  `std.crypto.sha3` ships only fixed SHA-3; ExpandA / ExpandS / ExpandMask
  / SampleInBall / SimpleBitPack / pkEncode), and
  `src/os/crypto/ml_dsa.spl` (KeyGen + Sign + Verify wrapper).
- **Spec coverage**: `test/unit/lib/crypto/ml_dsa_65_spec.spl`
  18/18 PASS in interpreter mode (66s) covering NTT round-trip, zetas
  table validation (NTT([1, 0, …, 0]) == [1; 256]), NTT pointwise
  multiplication vs direct convolution including the X^255 * X = -1
  negacyclic boundary, Power2Round / Decompose round-trips, MakeHint /
  UseHint property, BitPack 4-bit and 10-bit round-trip with size
  formulas, SHAKE-128("") and SHAKE-256("") byte-exact NIST FIPS 202 KAT,
  SampleInBall produces exactly τ=49 nonzero coefficients in {-1, 0, +1},
  KeyGen pk = 1952B and sk = 4032B (FIPS 204 §B Table for ML-DSA-65).
- **Side-channel discipline (per `feedback_no_coverups.md`)**: per-coefficient
  norm checks walk every coefficient with OR-accumulation (no early-out on
  first overflow); outer rejection-loop iteration count is intentionally
  variable (FIPS 204 §3.6 security analysis treats it as non-side-channel —
  κ never reused with a different message).  Verify's `c_tilde` comparison
  is byte-OR XOR.
- **End-to-end Sign+Verify DEFERRED** — Sign produces a 3293-byte signature
  but Verify currently rejects it.  Bug filed at
  `doc/08_tracking/bug/ml_dsa_sign_verify_pipeline_2026-05-02.md` with
  hint pack/unpack ordering and `make_hint_poly` polarity on negative-z
  inputs as the leading hypotheses.  Per `feedback_no_coverups.md` we did
  NOT weaken the spec to "verify returns a bool"; algebraic invariants
  cover the ring + NTT + sampling + encoding contract; Wave 11+ closes the
  end-to-end gate.
- **Performance** (interpreter mode, no native externs): ExpandA 12.6s,
  KeyGen 17.7s, Sign ~60s per attempt × ~1 attempt, Verify ~5s.  No FR
  filed yet — perf is in line with the FIPS 204 reference impl ratio
  given Simple's interpreter overhead and what Wave 11+ work needs is
  correctness, not speed.
- **NOT in scope for W10-A** (deferred to Wave 11+): ML-DSA-44, ML-DSA-87,
  deterministic-variant choice (default randomized per FIPS 204 §3.6),
  context-string parameter, pre-hash variants.
- **Ready for hybrid TLS 1.3 sigalg wiring next wave** (`ml_dsa_65 +
  ed25519` per draft RFC) once the Sign/Verify pipeline bug is resolved.
