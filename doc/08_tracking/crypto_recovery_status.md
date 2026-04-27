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

## Next Execution Order

1. Repair the TLS M3 live gaps on the existing `src/os/tls13` stack, starting with hosted mTLS and the env-gated QEMU live failures.
2. Add exact `openssl s_client -tls1_3`, `openssl s_server -tls1_3`, and `curl --tlsv1.3` coverage on top of the now-green default hosted gates.
3. Finish M4 by validating the HTTPS startup path end-to-end with browser/`wss://` smokes and deciding whether the existing rustls-backed `TlsWebServer` remains the production server backend.
4. Defer M5 PQ and M6 HTTP/2 until M3 and M4 are green.
