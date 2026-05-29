# Remains Report — After RSA-PSS + Poly1305 Wave (2026-04-16)

## Context

Session waves completed today on `main`:

| Commit | Landing |
|--------|---------|
| `6243cab928` | `rt_*_sign` empty-`[u8]` error contract |
| `0f42ec30b424` | Interpreter signature FFI dispatch |
| `4790555d7f1a` | SshDaemon RSA plumbing + `rt_ed25519_sign` + dedup |
| `e75cb06396a4` | RSA-SHA-256 + SHA-512 host-key specs + Ed25519 sign spec + PEM/DER loader + cargo `tls_test_server` bin + TLS1.2 install + Phase-2 backlog docs |
| `cf1f9d4122af` | 65 syscall-shim stubs (unblocks `bin/simple os build --scenario=tls-unit` link step) |
| `cdb8ad4b5fa6` | `SshDaemon` RSA demo + `_shell_command` harness helper |
| `a2c5361f5e04` | RSA-PSS verify end-to-end: runtime FFI + interpreter dispatch + Simple wrappers + `cert_verify.spl` scheme-aware dispatch + `extract_rsa_pubkey_spki_from_cert` |
| `04740fa6e705` | Poly1305 finalize sign-shift fix + `tls13.spl` state machine wired for scheme dispatch + RSA-PSS verify spec |

Per-layer state:

- **Runtime FFI (Rust):** `rt_*_verify` (rsa-256/384/512 PKCS1, rsa-pss-256/384/512, ed25519, ecdsa-p256), `rt_*_sign` (rsa-256/512, ed25519, ecdsa-p256). Symmetric modulo PKCS1-vs-PSS verify; ed25519 sign/verify both present. Empty-`[u8]` error contract uniform for sign.
- **Interpreter dispatch (Rust):** all signature FFIs explicitly dispatched (dynamic_ffi cannot marshal `[u8]`).
- **Simple wrappers (`signature_ffi.spl`):** Tier-2 wrappers align with empty-array-on-error contract.
- **TLS 1.3 client (`src/os/tls13/`):** record layer (AES-128-GCM), KEX (X25519), HKDF, transcript, handshake codec, cert-verify with Ed25519 + RSA-PSS {SHA-256, SHA-384, SHA-512}, state machine reads SignatureScheme from wire. No PSK, no mTLS, no 1.2 fallback, no server-side.
- **SSH daemon:** advertises `rsa-sha2-256,ssh-ed25519`; signs with whichever host key is configured. RSA PKCS#8 loader (PEM/DER autodetect) available via `SshDaemon.load_host_rsa_key`.
- **Crypto primitives:** all 27 tests in `os_crypto_ref_primitives_spec.spl` pass after Poly1305 fix.

## Remains — classified

### A. Blockers (not tractable as single agent waves)

1. **Compiler SMF emission broken.** Per memory rule (2026-04-16), `simple_mcp` / `lsp_mcp` wrappers run from `.spl` by default; SMF cache opt-in via `SIMPLE_MCP_USE_CACHE=1` because the compiler emits broken SMFs.
   - **Impact:** blocks the native integration-test runner (Wave D rejected 2026-04-16) and any path that compiles Simple `.spl` → native binary for execution.
   - **Remediation:** compiler-internal work — codegen + SMF serialization in `src/compiler/` and/or Rust seed pipeline. Not a single-agent task; needs its own scoped project.
   - **Files involved (pointers):** `src/compiler_rust/compiler/src/pipeline/native_project/`, `src/compiler/80.driver/`, `src/compiler/70.codegen/`.

2. **Interpreter `Option<[u8]>` wrapping at FFI sign sites.** 17 tests failing in `os_crypto_ref_signature_spec.spl` per `doc/09_report/crypto_spec_remains_2026-04-16.md`.
   - Concurrent session is actively working this (landed `_unwrap_sig` at `8ddbe1b5273b`, plus `_rsa_unwrap`/`_ecdsa_unwrap` helpers; further work in-flight).
   - **Do not collide** — parallel-scope-partition memory rule applies. Wait for their commit; pick up whatever remains.

3. **`qemu-system-x86_64` not installed on dev host.** Blocks `os_tls_spec.spl` and `os_tls_system_spec.spl` end-to-end runs.
   - Ops, not code. Install path documented at `doc/01_research/local/qemu_install_notes.md`.

### B. Tractable follow-ons (each a sonnet-agent wave when prioritized)

4. **Run `os_tls_spec.spl` + `os_tls_system_spec.spl`** end-to-end.
   - Preconditions: #3 (qemu installed). The wave-1 linker fix (cf1f9d4) got the kernel building; wave cdb8ad4 added `_shell_command` helper; together these unblock past the link + harness steps.
   - Execution alone is ~one agent if prerequisites met. If the `[TLS HANDSHAKE COMPLETE]` sentinel fires against the rustls test server, Phase 1 TLS ships.

5. **Cert-chain verification for intermediate CAs.** Currently `cert_verify.spl` handles the leaf `CertificateVerify` only; a real TLS 1.3 handshake needs walking up a chain of issuer certs with their own RSA-PSS signatures.
   - New function `verify_cert_chain(chain: [[u8]], root_store: [[u8]]) -> CertChainResult` in `cert_verify.spl`.
   - Infrastructure all exists: SPKI extraction works, RSA-PSS verify works, DER walker works.
   - Estimated effort: M.

6. **RSA-PSS mixed-size interop.** Ring's `RSA_PSS_2048_8192_SHA256` etc. accept moduli 2048..8192 bits. No test covers 4096-bit or 8192-bit keys — purely additional test coverage, not new code.
   - Estimated effort: S.

7. **`rt_ed25519_sign` spec has no determinism fuzz beyond 2 repetitions.** Could add an RFC 8032 standard test vector round-trip.
   - Estimated effort: S.

8. **SSH host-key demo example** at `examples/ssh_rsa_hostkey/main.spl` has no automated spec covering it. Could add a driver that boots the daemon with a test PEM, connects an SSH client, captures the rsa-sha2-256 signature, verifies.
   - Depends on: SSH client-side test infrastructure; probably blocked on the same native-mode issue.
   - Estimated effort: M.

### C. Phase 2 (deferred by design)

Cross-reference: `doc/01_research/local/tls13_phase2_backlog.md`.

Advisor-recommended priority order for when Phase 2 starts:

9. **PSK resumption (1-RTT).** Needs NewSessionTicket handling + resumption-master-secret; open question on session ticket storage (in-memory vs VFS).
10. **Client certificates (mTLS).** Needs CertificateRequest parsing + signed_data construction + local cert/key storage; additive to cert_verify infra.
11. **TLS 1.2 fallback.** Largest effort — separate record layer (CBC/CTR+HMAC), separate key schedule (PRF), cipher-suite negotiation, `downgrade_protection` sentinel handling.
12. **0-RTT early data.** Security-sensitive (replay attack surface); advisor suggested never enable in Phase 2, 1-RTT PSK only.
13. **Server-side TLS 1.3.** Not currently implemented; no known caller. Defer until browser-platform HTTPS termination or similar driver emerges.

### D. Open decisions (block Phase 2 start)

Before any Phase 2 wave begins, the user should decide:

- **RSA-PSS crate choice for Phase 2 features** — `ring` was chosen for Phase 1 verify (already vendored at 0.17). Should Phase 2 sign-side additions (e.g. mTLS client sign) also use `ring`, or does a no_std / baremetal re-implementation become necessary for SimpleOS side?
- **Session ticket storage** — in-memory (per-session, lost on restart) vs VFS-backed (durable, caps on ticket count). Interacts with #9.
- **0-RTT early data policy** — never (safer) vs idempotent-only (latency win, replay caveats). Interacts with #9.
- **Server-side TLS in Phase 2 scope?** — Would be needed if HTTPS-terminating services (e.g. browser platform) land in the near term.

## Recommended next actions

In order of highest-value-per-effort:

1. **Wait on concurrent session's interpreter-Option<[u8]> fix** (#2) — they're closer to done than anyone else can get on it.
2. **Install `qemu-system-x86_64`** (#3) — 1 command, unblocks #4.
3. **Run the two TLS specs** (#4) — closes the Phase 1 loop; reports whether TLS 1.3 actually handshakes against rustls.
4. **Scope a compiler-SMF fix project** (#1) — this is the meta-blocker for compiled-mode testing across the codebase, not just crypto. Deserves its own design document + wave structure.

Everything else is additive and can wait for a Phase 2 kickoff with decisions from §D.

## Related reports

- `doc/09_report/crypto_spec_remains_2026-04-16.md` — concurrent session's diagnostic for Poly1305 (fixed this session) + interpreter Option<[u8]> wrapping (in-flight).
- `doc/01_research/local/tls13_phase2_backlog.md` — Phase 2 design backlog.
- `doc/01_research/local/qemu_install_notes.md` — QEMU install commands per OS.
