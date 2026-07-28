# SSH Native Survey — lane SSHNAT

Date: 2026-07-27. Read-only assessment. No source modified, nothing committed.
Raw run logs: `build/sshnat_out/{jit_run.log,interp_run.log,kat_run.log}`.

## Headline

The roadmap line "OpenSSH port is the production path (multi-week, blocked)" is
**wrong on the server side and misleading on the client side.**

- A **pure-Simple SSH server** (`src/os/apps/sshd/`, 9,576 lines / 27 files) is
  substantially complete and is exercised by a live QEMU gate that drives a
  **real OpenSSH client** against it (`src/os/ssh_qemu_contract.spl:25`,
  `test/03_system/os/ssh_live_login_in_qemu_spec.spl:84`). Interop with stock
  OpenSSH is therefore already demonstrated, not aspirational.
- A **pure-Simple SSH client** also already exists —
  `src/os/tools/net/_SshTool/{transport.spl,run.spl}` (1,045 lines) — and it
  reuses the server's protocol core rather than duplicating it. It is *not*
  built on libssh2.
- The `ssh_sffi.spl` / `ssh_ffi.spl` "libssh2 client" is a **dead facade**:
  every `rt_ssh_*` extern it declares resolves only to NOP / weak-nil stubs
  (`examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c:2130`,
  `.../auto_stubs.c:3428`). There is no libssh2 dependency to remove, because
  there is no libssh2 binding.

So "port OpenSSH" is not the production path. The production path is
**finishing the pure-Simple stack that is already 10,600 lines deep**, and the
remaining work is bounded, not multi-week-blocked.

## Inventory 1 — server (`src/os/apps/sshd/`, 9,576 lines)

| SSH layer | Item | Status | Evidence |
|---|---|---|---|
| Transport | Version string build/parse | implemented | `ssh_transport.spl:190`, `:245` |
| Transport | Binary packet protocol (build/read/pad) | implemented | `ssh_packet.spl:214`, `:254`, `:257` |
| Transport | Wire types u32/string/mpint/bool/name-list | implemented | `ssh_packet.spl:53-206` |
| Transport | KEXINIT build/parse | implemented | `ssh_transport.spl:277`, `:318` |
| Transport | Algorithm negotiation | implemented | `ssh_transport.spl:501` |
| Transport | `ext-info-s` + SSH_MSG_EXT_INFO (server-sig-algs) | implemented | `ssh_transport.spl:591`, `:65` |
| Transport | `kex-strict-s-v00@openssh.com` (Terrapin mitigation) | implemented | `ssh_transport.spl:41`, `:497` |
| Transport | SERVICE_REQUEST/ACCEPT, DISCONNECT | implemented | `ssh_transport.spl:584`, `:629`, `:645` |
| Transport | Rekeying (mid-session KEXINIT) | partial — client-initiated rekey is handled (`ssh_session.spl:749` re-runs `do_kex()`); the server never initiates one, no byte/time threshold exists | `ssh_session.spl:749-751`; zero hits for any rekey threshold/counter |
| Transport | Compression (zlib / zlib@openssh.com) | **absent** (none only) | zero `zlib` hits |
| KEX | curve25519-sha256 (RFC 8731) | implemented | `ssh_transport.spl:41`, `ssh_kex_core.spl:35-42` |
| KEX | Exchange hash H | implemented | `ssh_kex_core.spl:50` |
| KEX | Key derivation (A..F) | implemented | `ssh_kex_core.spl:72`, `:95` |
| KEX | KEX_ECDH_INIT parse / REPLY build / NEWKEYS | implemented | `ssh_kex.spl:136`, `:118`, `:150` |
| KEX | diffie-hellman-group* fallback | **absent** | zero hits |
| Host key | ssh-ed25519 sign | implemented | `ssh_kex_crypto.spl:372`, `ssh_session_kex.spl:675` |
| Host key | rsa-sha2-256 / rsa-sha2-512 sign | implemented | `ssh_kex_crypto.spl:352` (`ssh_sign_exchange_hash`) |
| Host key | ecdsa-sha2-nistp256 sign | implemented | `ssh_kex_crypto.spl:401`, blob at `:209` |
| Host key | OpenSSH cert-v01 algorithms advertised | partial (advertised, no cert validation) | `ssh_kex.spl:53` |
| Host key | PEM/DER PKCS#8 loader | implemented | `host_key_loader.spl:98`, `:68` |
| Cipher | aes256-gcm@openssh.com | implemented | `ssh_cipher_live.spl:87`, `:163` (live) / `ssh_cipher.spl:112`, `:152` (pure) |
| Cipher | aes128-gcm@openssh.com | implemented | `ssh_cipher_live.spl:125`, `:236` |
| Cipher | aes256-ctr + hmac-sha2-*-etm | implemented, pure Simple | `ssh_cipher.spl:304`, `:321` |
| Cipher | **two cipher modules, only one is pure Simple** | see note | `ssh_cipher.spl` (502 lines) is pure — it imports `os.crypto.{aes_gcm, chacha20, chacha20_poly1305, random}` (`:18-21`) and is what the pure-Simple **client** uses. The live **server** session uses `ssh_cipher_live.spl` instead (`ssh_session.spl:20`), whose AES-GCM is C: `rt_tls13_aes256_gcm_encrypt/decrypt`, `rt_ssh_aes256_gcm_decrypt_packet` (`ssh_cipher_live.spl:9-12`) implemented in `examples/09_embedded/simple_os/arch/{x86_64,riscv64}/boot/tls13_aes256_gcm_helper.c` (140 / 485 lines). So the shipped server's bulk-crypto hot path is C-accelerated, not pure Simple. |
| Cipher | chacha20-poly1305@openssh.com | partial — the primitive is imported by `ssh_cipher.spl:20` but the OpenSSH algorithm name is never offered in KEXINIT, so the suite is not negotiable | zero hits for the algorithm string in the tree |
| MAC | hmac-sha2-256-etm / hmac-sha2-512-etm, constant-time verify | implemented | `ssh_mac.spl:77`, `:102`, `:89` |
| Userauth | `none` + failure/banner replies | implemented | `ssh_auth.spl:258-296` |
| Userauth | password, constant-time compare | implemented | `ssh_auth.spl:37` (`authenticate_password`), `ssh_session_auth.spl:29` |
| Userauth | password store | **plaintext**, no bcrypt/PBKDF | `ssh_auth.spl:62` "plaintext storage for baremetal" |
| Userauth | publickey — request parse + PK_OK probe | implemented | `ssh_auth.spl:198-251`, `:310` |
| Userauth | publickey — **signature verification** | **ABSENT / DISABLED** | `ssh_auth.spl:354-357`: "Public key authentication is currently DISABLED in ssh_session.spl. To enable it, implement Ed25519 signature verification for userauth here." |
| Userauth | keyboard-interactive (INFO_REQUEST/RESPONSE) | partial (encode/decode only, no challenge loop) | `ssh_auth.spl:227`, `:327`, `:339` |
| Userauth | MAX_AUTH_ATTEMPTS throttle | implemented | `ssh_auth.spl` export list |
| Connection | Channel table, open/confirm/failure | implemented | `ssh_channel.spl:66`, `:193`, `:322`, `:332` |
| Connection | DATA / EXTENDED_DATA / EOF / CLOSE / WINDOW_ADJUST | implemented | `ssh_channel.spl:232-379` |
| Connection | `exec` request | partial — routed resolver, not a general spawn | `ssh_session_channel.spl:232-262` (special-cases `true` and a fixed rv64 probe string, then routes argv to the SMF/FS-ELF resolver) |
| Connection | `shell` request + PTY | **partial, and the interactive bridge is RED at HEAD** — `ssh_session_shell_spec.spl` is 5/7; both `echo` round-trips fail because the adapter returns only the banner and prompt and never runs the command (`expected "SimpleOS Shell v0.2 … user@simpleos:/# $ " to contain "ssh"` for input `"echo ssh\n"`). The 5 green `it`s are all SMF/exec *resolution*, not interactive execution. | `ssh_pty.spl:20` (`SshPty`, resize at `:167`), `ssh_remote_shell.spl` (59 lines), `test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl:20`, `:25` |
| Connection | `env`, `window-change`, `exit-status` | implemented | `ssh_session_channel.spl:390`, `:474`, `ssh_session.spl:1117` |
| Connection | `subsystem` / sftp | **absent** | zero hits |
| Connection | port forwarding (direct-tcpip / tcpip-forward) | **absent** (type string recognised in a comment only) | `ssh_channel.spl:198` |
| Connection | X11 forwarding, agent forwarding | **absent** | zero hits |
| Daemon | bind/accept loop, host key selection, user db | implemented | `sshd.spl:326`, `:494`; externs `rt_boot_tcp_bind` / `rt_boot_tcp_accept_timeout` at `sshd.spl:30-31`, implemented in `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:8169`, `:8196` |
| Daemon | privilege separation | **absent** | — |

## Inventory 2 — client

### 2a. Pure-Simple client — `src/os/tools/net/_SshTool/` (1,045 lines)

Shares the server's protocol core (`use os.apps.sshd.{ssh_transport, ssh_packet,
ssh_kex, ssh_cipher, ssh_auth, ssh_channel}` — `transport.spl:10-55`,
`run.spl:10-55`), which is why it is thin.

| Item | Status | Evidence |
|---|---|---|
| TCP socket + framing | implemented (host externs) | `transport.spl:76-79`, `:81` |
| Version exchange | implemented | `transport.spl:193` |
| KEXINIT send/parse | implemented | `run.spl:157-180` |
| KEX ECDH (curve25519) + ECDH_REPLY parse | implemented | `run.spl:183`, `transport.spl:372` |
| Key derivation + NEWKEYS | implemented | `run.spl:225`, `:251` |
| Encrypted send/recv (AES-GCM) | implemented | `transport.spl:219`, `:234` |
| Post-NEWKEYS EXT_INFO/IGNORE/DEBUG skip | implemented | `transport.spl:296` |
| Host key **signature** verification | implemented, but via SFFI | `run.spl:242` → `std.io.signature_sffi.verify_host_key` (`src/lib/nogc_sync_mut/io/signature_sffi.spl:275`) |
| `known_hosts` / TOFU pinning | **absent** — signature is checked, key identity is not | no known-hosts logic in `_SshTool` |
| userauth password | implemented | `transport.spl:480` |
| userauth publickey | **absent** | — |
| channel open + pty-req + shell + I/O loop | implemented | `run.spl:347-393` |
| `exec` (non-interactive) | **absent** (shell only) | `run.spl:384` |
| Wired into the SimpleOS shell | **NO — registered as a stub** | `src/os/tools/shell/register_tools.spl:91` `fn _run_ssh(args) -> i32: _run_unavailable("ssh")`, registered at `:258`. `run_ssh` is never called. |
| Test coverage | **1 spec, 1 describe, @cover 30%** | `test/01_unit/os/tools/net/ssh_version_spec.spl:1`, `:19` — only `ssh_build_version_string` |

### 2b. SFFI "libssh2" client — dead facade

| Item | Status | Evidence |
|---|---|---|
| `src/lib/{nogc,gc}_{sync,async}_mut/io/ssh_sffi.spl` (384 lines × 4 tiers) | API surface only | 20 externs: `rt_ssh_connect`, `rt_ssh_auth_password/pubkey/agent`, `rt_ssh_exec`, `rt_ssh_shell`, `rt_ssh_channel_*`, `rt_ssh_forward_*`, `rt_ssh_check_host_key`, … |
| `src/app/io/ssh_ffi.spl` | API surface only | same externs |
| Any Rust/C implementation of `rt_ssh_*` | **none anywhere in the repo** | repo-wide search excluding `target/` and `vendor/` finds only the two `.spl` declarations and the stub files below |
| Guest stubs | NOP / weak-nil | `examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c:2130-2140` (`NOP4(rt_ssh_connect)` …), `auto_stubs.c:3428-3431` (`__attribute__((weak)) … return NIL_VALUE`) |
| `ssh2` / `libssh2` crate dependency | **not present** in any Cargo.toml | — |

This is exactly the weak-nil-stub failure mode recorded in memory
(`auto_stubs.c` WEAK `rt_*` stubs): the API compiles and links, and every call
silently returns nil.

## Spec verdicts

Runner: `bin/simple test <spec> [--mode=interpreter] --timeout 900`.
**Landmine hit:** without an explicit `--timeout`, the runner's own default
kills long specs with "Process timed out" and exit 255 — the first pass reported
false reds for `ssh_kex_hostkey_matrix_spec` and `ed25519_rfc8032_spec` for this
reason alone. All verdicts below are from the re-run with `--timeout`.

**A/B result: the JIT and `--mode=interpreter` runs are byte-identical across
all 20 specs** — same totals, same passes, same failures, same messages. No
engine-specific behaviour anywhere in this tree, so every red below is a real
defect in the code or the specs, not an engine artifact.

Totals: **20 specs, 124 examples, 94 passed, 30 failed. 13 specs green, 7 red.**

| Spec | Total | Pass | Fail | Verdict |
|---|---:|---:|---:|---|
| `01_unit/os/apps/sshd/ssh_auth_password_spec.spl` | 6 | 6 | 0 | GREEN — constant-time password auth |
| `01_unit/os/apps/sshd/ssh_ct_auth_compare_spec.spl` | 10 | 10 | 0 | GREEN — 2 describes, constant-time byte + password-field compare |
| `01_unit/os/apps/sshd/sshd_spec.spl` | 7 | 7 | 0 | GREEN — 2 describes, runtime int decoding + host key selection |
| `01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` | 7 | 1 | 6 | **RED** — missing export; only the X25519 `it` runs; 6 describes never execute |
| `01_unit/os/apps/sshd/ssh_kexinit_packet_layout_spec.spl` | 9 | 9 | 0 | GREEN — 3 describes, RFC 4253 §6 + §7.1 payload/packet layout |
| `01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl` | 1 | 0 | 1 | **RED** — missing export |
| `01_unit/os/apps/sshd/ssh_mac_spec.spl` | 10 | 10 | 0 | GREEN — 2 describes, constant-time MAC verify + property |
| `01_unit/os/apps/sshd/ssh_packet_malformed_spec.spl` | 17 | 17 | 0 | GREEN — 3 describes, bounds + malformed-input hardening |
| `01_unit/os/apps/sshd/ssh_packet_spec.spl` | 10 | 10 | 0 | GREEN — 3 describes, build / read errors / mpint |
| `01_unit/os/apps/sshd/ssh_session_shell_spec.spl` | 7 | 5 | 2 | **RED** — interactive shell bridge never executes the command |
| `01_unit/os/apps/sshd/ssh_transport_spec.spl` | 15 | 15 | 0 | GREEN — 2 describes, KEXINIT parsing + algorithm negotiation |
| `01_unit/os/crypto/ed25519_ssh_exchange_hash_spec.spl` | 1 | 0 | 1 | **RED** — `no examples executed` |
| `01_unit/os/tools/net/ssh_version_spec.spl` | 4 | 4 | 0 | GREEN — the pure-Simple client's only spec |
| `01_unit/os/x86_ssh_boot_tcp_contract_spec.spl` | 2 | 2 | 0 | GREEN — x86 SSH boot contracts |
| `02_integration/.../sshd_production_packet_transcript_spec.spl` | 1 | 0 | 1 | **RED** — missing export; full-session walk dead |
| `02_integration/.../sshd_production_session_kexinit_spec.spl` | 2 | 0 | 2 | **RED** — real assertion failures; host-key advertisement ignores policy |
| `03_system/os/os_ssh_host_key_loader_spec.spl` | 8 | 8 | 0 | GREEN — 4 describes, PEM + DER + errors + daemon load |
| `03_system/os/os_ssh_rsa_hostkey_spec.spl` | 3 | 0 | 3 | **RED** — missing export |
| `03_system/os/os_ssh_rsa_sha512_hostkey_spec.spl` | 3 | 0 | 3 | **RED** — missing export |
| `03_system/os/os_ssh_spec.spl` | 1 | 0 | 1 | **RED** — `no examples executed` |

**Shape of the 30 failures: 14 of them are one missing `export`.** Strip that
out and the real defect count is small: the shell bridge (2), the host-key
advertisement policy (2), and two specs that register no examples (2).

What is genuinely proven green: the binary packet protocol and its malformed-input
hardening (27 examples), KEXINIT build/parse/negotiate and RFC 4253 layout (24),
constant-time password auth and MAC verify (26), PEM/DER host-key loading (8).
That is a solid, well-tested protocol *core*.

What is not proven at all: host-key **signing** for every algorithm
(ed25519/rsa-sha2-256/rsa-sha2-512/ecdsa-p256), the full-session transcript, and
Ed25519 verification.



The two QEMU live-login specs (`test/03_system/os/ssh_live_login_in_qemu_spec.spl`,
`.../rv64_ssh_live_login_in_qemu_spec.spl`) were **not run** in this lane: each
builds a Cranelift guest kernel and boots QEMU, which is outside a survey lane's
budget. Their recorded evidence contract is real, though — see
`doc/06_spec/system/ssh_live_login_in_qemu_spec.md` (host port 2222 → guest 22,
real `ssh` binary with `-o HostKeyAlgorithms=ssh-ed25519,rsa-sha2-256,rsa-sha2-512`,
good-auth / bad-auth / two exec probes, transcripts under
`build/os/x64-ssh-live.*`). No `build/os/*ssh*` artifacts exist in this
worktree, so the gate has not been run here recently.

### Defect found: the host-key signing matrix is dead at HEAD (missing re-export)

`test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` reports
**1 passed, 6 failed** on both engines. Every failure is the same message:

```
semantic: function `ssh_sign_exchange_hash` not found
```

Cause: the spec imports it at line 45 —
`use os.apps.sshd.ssh_kex.{HostKeySet, ssh_sign_exchange_hash, …}` — but
`ssh_sign_exchange_hash` is defined in the *sibling* module
`src/os/apps/sshd/ssh_kex_crypto.spl:352` and **`ssh_kex.spl` never re-exports
it**. The string `ssh_sign_exchange_hash` appears zero times in
`src/os/apps/sshd/ssh_kex.spl`; its export list (`:156-159`) omits it.

This is **not** an Ed25519 crypto defect — the one `it` in that describe that
does not call the missing function ("derives 32-byte X25519 public keys and a
matching shared secret") passes, and Ed25519 signing byte-matches RFC 8032 in
the KAT run below.

Impact is larger than the 6 reds: the spec aborts after 7 `it`s, so the
**rsa-sha2-256, rsa-sha2-512, ecdsa-sha2-nistp256, unknown-algorithm,
KEXINIT-builder and advertised-algorithms describes never execute at all**.
The entire host-key signing matrix — the thing that proves the server can
authenticate itself to a client — is currently unverified by unit specs.

The same missing export kills **three specs in total**:

| Spec | Result | Killed example |
|---|---|---|
| `test/01_unit/os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl` | 7 total, 1 passed, 6 failed | 6 ed25519 `it`s, plus 6 whole describes (rsa-sha2-256/512, ecdsa-p256, unknown-algo, KEXINIT builder, advertised algorithms) that never execute |
| `test/01_unit/os/apps/sshd/ssh_kex_rsa_contract_spec.spl` | 1 total, 0 passed, 1 failed | `produces a rsa-sha2-512 blob that verifies with a real RSA key` |
| `test/02_integration/os/apps/sshd/sshd_production_packet_transcript_spec.spl` | 1 total, 0 passed, 1 failed | `walks version, KEX, NEWKEYS, service, password auth, and channel packets` — **the whole end-to-end protocol transcript** |

That third one is the most damaging: the integration test that walks a complete
session end to end is dead, so the only surviving end-to-end evidence for the
server is the QEMU live gate. One missing `export` line is what stands between
the project and (a) any proof that RSA/ECDSA host-key signing works and (b) its
only in-process full-session test.

Verified pre-existing, not caused by this lane: `git status` reports
`ssh_kex.spl`, `ssh_kex_crypto.spl` and both specs clean vs HEAD.
Both engines (JIT and `--mode=interpreter`) produce byte-identical verdicts
here, which rules out an engine artifact.

Fix is one line (add `ssh_sign_exchange_hash` to the `export` list in
`ssh_kex.spl`), but it is a source change and therefore out of scope for this
read-only lane. **This should be the first item picked up.**

### Second defect: host-key algorithm advertisement ignores daemon policy

`test/02_integration/os/apps/sshd/sshd_production_session_kexinit_spec.spl` is
**2 total, 0 passed, 2 failed** — and unlike the export problem above, these are
real assertion failures, not resolution errors:

```
✗ uses daemon-selected host material and certificates for accepted sessions
    expected  ssh-ed25519-cert-v01@openssh.com,ssh-ed25519
    to equal  ssh-ed25519-cert-v01@openssh.com,ssh-ed25519,rsa-sha2-256-cert-v01@openssh.com

✗ does not advertise raw Ed25519 when the production daemon disables it
    expected  ssh-ed25519
    to equal  rsa-sha2-256,rsa-sha2-512
```

The second one is the security-relevant half: **the daemon advertises
`ssh-ed25519` even when configuration disables it**, i.e. a host-key algorithm
restriction is silently not honoured. The first shows configured RSA cert
material never reaching the advertised list. Together these say
`host_key_set_advertised_algorithms` / the KEXINIT builder do not respect
daemon policy — and note that the unit spec which would have localised this
(`host_key_set_advertised_algorithms` describe in the matrix spec) is one of
the describes killed by the missing export, so this only surfaced at the
integration layer.

### Coverage shape — proven vs merely present

Only 5 of the 27 server files carry an `@cover` declaration:
`ssh_packet.spl` 75%+50%, `ssh_transport.spl` 75%, `ssh_auth.spl` 40%,
`ssh_kex.spl` 70%, `ssh_mac.spl` 60%. Those five files are **1,622 of the
9,576 lines — 17%**.

The other ~7,950 lines have no unit-spec coverage target at all, including the
largest and most stateful modules: `ssh_session.spl` (1,485),
`ssh_session_kex.spl` (804), `ssh_session_helpers.spl` (801),
`ssh_session_channel.spl` (647), `ssh_kex_primitives.spl` (637),
`sshd.spl` (593), `ssh_cipher.spl` (502), `ssh_channel.spl` (388),
`ssh_cipher_live.spl` (285), `ssh_pty.spl` (180).

So the honest reading is: **the protocol primitives are proven by unit specs;
the session state machine is proven only by the QEMU live-login gate** — a
single end-to-end test that this lane did not run. That is real evidence (it
drives a stock OpenSSH client), but it is one path through the machine, and it
is the only thing standing behind 83% of the code.

Orphaned generated matcher files with no source spec (dead scaffolding worth a
cleanup, not a defect): `test/01_unit/os/apps/sshd/.spipe_wrapped_entry_ssh_cipher_live_aes256_gcm_spec.spl`,
`.spipe_wrapped_entry_ssh_transport_ext_info_spec.spl`,
`test/02_integration/os/apps/sshd/.spipe_matchers_ssh_aes256_gcm_packet_spec.spl`,
`.spipe_matchers_ssh_kdf_parity_spec.spl`.

## Crypto dependency status

Every crypto primitive an SSH implementation needs, run on the default engine
with `--timeout 1500`. Log: `build/sshnat_out/kat_run.log`.

| SSH role | Primitive | Spec | Verdict |
|---|---|---|---|
| KEX | curve25519 / X25519 | `curve25519_rfc7748_spec.spl` | **9/10** — all RFC 7748 TV1/TV2 vectors and both ECDH-agreement directions PASS. Sole red is `BigInt probe matches the live C helper bootstrap public key`, an internal backend-parity probe, not an RFC vector. **KEX crypto is proven.** |
| Cipher | ChaCha20-Poly1305 | `chacha20_poly1305_rfc8439_spec.spl` | **12/12 PASS** |
| Cipher | AES-256-GCM | `aes256_gcm_nist_vectors_spec.spl` | **12/12 PASS** |
| MAC | HMAC (SHA-224/256/384/512) | `hmac_rfc4231_spec.spl` | **12/12 PASS** |
| KDF | HKDF | `hkdf_rfc5869_spec.spl` | **9/9 PASS** |
| Host key | RSA PKCS#1 v1.5 | `rsa_pkcs1_v15_spec.spl` | **10/10 PASS** |
| Hash | SHA-256 / SHA-512 | `sha2_nist_vectors_spec.spl` | **2/8** — but both reds are `semantic: function sha256_hex / sha512_hex not found`, i.e. missing exports again, **not** wrong digests. The two `it`s that call the byte-level API directly (1024-byte multi-block SHA-256 and SHA-512) both PASS. |
| Host key + userauth | Ed25519 | `ed25519_rfc8032_spec.spl` | **2/3, and only 3 of the spec's 15 `it`s ever ran.** `derived public key matches RFC 8032 §7.1` PASS and `sign(empty) byte-matches RFC 8032 §7.1 expected signature` PASS — **signing is byte-exact against the RFC.** The run then dies inside the third `it`, `T1: signature verifies under the correct public key`, with no assertion message; the serial trace stops mid-`[ed25519-sc] reduce`, i.e. `ed25519_verify` aborts the runner. 67s wall. |

**Read of the Ed25519 result.** Ed25519 *signing* — what the server needs to
authenticate itself — is proven byte-exact. Ed25519 *verification* — what
publickey userauth (S1) and the client's host-key check (C2) both depend on —
crashes the runner in `src/lib/common/crypto/ed25519.spl`. Note this is the
`std`/`common` copy; the sshd uses the separate `os.crypto` copy
(`src/os/crypto/ed25519.spl:444`), whose verify path is exercised by
`test/01_unit/os/crypto/ed25519_ssh_exchange_hash_spec.spl` (4 `ed25519_verify`
call sites).

I ran that spec. It reports **`error: test-runner: no examples executed`**
(1 total, 0 passed, 1 failed, EXIT=1) on the default engine — it registers
zero examples, so it proves nothing either way. Its first `it` calls
`ed25519_sign` then `ed25519_verify`, the same shape that aborts the runner in
the `std` copy, which is suggestive but not conclusive; the output carries no
error beyond lint warnings.

**Net: Ed25519 verification is unproven in BOTH copies at HEAD** — the `std`
copy aborts the runner mid-verify, and the `os.crypto` copy's only spec runs
nothing.

**Cause identified (credit: the parallel `.spipe/ssh_native_client/` lane).**
`os.crypto.ed25519` **cannot be JIT-lowered at HEAD** — `HIR lowering error:
Unknown type: u128`. That explains the `no examples executed` result here
exactly: the spec cannot lower, so it registers nothing. It also has a nasty
second-order effect that lane documents — any spec transitively importing
`os.crypto.ed25519` silently runs on the *interpreter* even when you ask for
the JIT, **so a JIT/interpreter A/B of anything Ed25519-touching is not
actually possible right now**. My "A/B identical across all 20 specs" result
above is therefore honest but weaker than it looks for the Ed25519-touching
subset: those specs ran the same engine twice.

Revised read: Ed25519 verify is not necessarily *wrong*, it is *unlowerable*.
Closing the `u128` gap is the prerequisite for both S1 and C2 and for any
meaningful A/B of them. Until then treat "Ed25519 verify works" as unproven,
and note the client lane reports ~3s per Ed25519 op for the same reason.

### Cross-cutting theme: missing exports are silently voiding test coverage

Three separate reds in this survey — `ssh_sign_exchange_hash` (2 spec files),
`sha256_hex`, `sha512_hex` — are all the same failure mode: a spec imports a
symbol the module never exported, so the `it` reports as a *test failure*
rather than a *build error*, and the coverage it was meant to provide silently
evaporates. This is worth a repo-wide sweep: grep every spec's `use` list
against the exports of the module it names. It is cheap and it is currently
hiding the host-key signing matrix and half the SHA-2 KATs.

Pure-Simple crypto exists at two addresses — `src/lib/common/crypto/` (26 files,
60 spec files under `test/01_unit/lib/crypto/`) and `src/os/crypto/` (105 files,
46,404 lines) — and the sshd uses the `os.crypto.*` copy. `os.crypto.ed25519`
declares a few accelerator externs (`rt_ed25519_sc_reduce_64`,
`rt_ed25519_sc_muladd`, `rt_ed25519_sign_seed`, `rt_tls13_sha512_full` —
`src/os/crypto/ed25519.spl:24-27`); those are guest-runtime hot paths, not the
whole algorithm, and `ed25519_verify` is defined in Simple at
`src/os/crypto/ed25519.spl:444`.

## Verdict: bounded, not multi-week

A pure-Simple, in-guest SSH **server** is ~90% done and already interops with
stock OpenSSH. A pure-Simple, in-guest SSH **client** is ~75% done and is 1,045
lines of glue on top of the same core; what it is missing is small and named.

The three things that actually block "in-guest ssh client" are each a
day-scale item, not a protocol port:

1. `rt_io_tcp_connect` is a NOP in the guest
   (`examples/09_embedded/simple_os/arch/x86_64/boot/rt_extras.c:1841`) while
   the *server* side (`rt_boot_tcp_bind` / `rt_boot_tcp_accept_timeout`) is
   fully implemented in `baremetal_stubs.c:8169`/`:8196`. Outbound connect is
   the single missing runtime primitive.
2. `verify_host_key` is SFFI (`std.io.signature_sffi`), whose `rt_ed25519_verify`
   is likewise a guest NOP. The pure-Simple replacement already exists and is
   already used by the sshd: `os.crypto.ed25519.ed25519_verify`.
3. The shell's `ssh` entry is a stub — `register_tools.spl:91` returns
   `_run_unavailable("ssh")` instead of calling `run_ssh`.

Nothing here requires writing SSH protocol code. Porting OpenSSH (C, ~120k
lines, needs fork/privsep/PAM) would be *strictly more* work than finishing
this, and would not be pure Simple.

## Ordered plan

Server (production hardening — highest security value first):

- **S0. Add `ssh_sign_exchange_hash` to the `export` list in
  `src/os/apps/sshd/ssh_kex.spl`.** One line. It resurrects 6 dead `it`s and
  unblocks 6 whole describes (rsa-sha2-256/512, ecdsa-p256, unknown-algo,
  KEXINIT builder, advertised algorithms) that currently never run. Do this
  before anything else — right now nobody knows whether RSA and ECDSA host-key
  signing work, because the tests that would say so cannot even resolve.
- **S0b. Fix `HIR lowering error: Unknown type: u128` in `os.crypto.ed25519`.**
  Prerequisite for S1, C2, and for any honest JIT/interpreter A/B of Ed25519
  code (today such specs silently run interpreter-only). Also the reason each
  Ed25519 op costs ~3s.
- **S1. Enable publickey userauth.** Implement RFC 4252 §7 signed-blob
  reconstruction and call `os.crypto.ed25519.ed25519_verify` at the site
  `ssh_auth.spl:354` already points at. Add rsa-sha2-256/512 via the existing
  `ssh_kex_crypto` verify path. *Est. 1–2 days after S0b.* Until this lands the
  server is password-only, which is why the ledger should not say "production".
- **S1b. Fix host-key advertisement policy** (the `sshd_production_session_kexinit`
  reds): the daemon advertises `ssh-ed25519` when config disables it, and
  configured RSA cert material never reaches the advertised list. Security-
  relevant and independent of everything else.
- **S2. Replace plaintext password storage** (`ssh_auth.spl:62`) with a KDF —
  `src/os/crypto/bcrypt.spl` and `argon2.spl` both already exist.
- **S3. Server-initiated rekey.** Client-initiated rekey already works
  (`ssh_session.spl:749`); what is missing is the server's own byte/time
  threshold, so a long session or a large transfer never rotates keys.
  *Est. 1–2 days.*
- **S4. Generalise `exec`.** Remove the special-cased command strings at
  `ssh_session_channel.spl:242-250` so argv routes uniformly through the
  FS-ELF/SMF resolver.
- **S5. Optional interop breadth:** offer chacha20-poly1305@openssh.com in
  KEXINIT — `ssh_cipher.spl:20` already imports the primitive, only the
  algorithm-name plumbing is missing; then `subsystem`/sftp and port forwarding.
- **S6. Converge the two cipher modules.** `ssh_cipher.spl` (pure) and
  `ssh_cipher_live.spl` (C helper) implement the same suites twice and can
  drift. Keep the C path as an explicit accelerator behind the pure interface
  rather than a parallel implementation the live session picks directly.

Client (to make `ssh` usable in-guest):

> **Update — a parallel lane acted on this.** `.spipe/ssh_native_client/`
> reports a new pure-Simple client tree `src/os/apps/ssh_client` (7 modules,
> ~1500 lines) that reuses the sshd `ssh_packet` / `ssh_transport` /
> `ssh_kex_core` verbatim and adds exactly the two gaps this survey named:
> **known_hosts pinning** (C5 — which I flagged as MITM-able) and **pure-Simple
> ed25519 host-key verification** replacing the SFFI `verify_host_key` (C2).
> 45 examples, 0 failures, in-process client↔sshd handshake proven. Still
> missing: record layer, socket wiring, live gate. That leaves **two** client
> trees, so C1/C3 below now mean wiring `_SshTool`'s socket I/O to delegate
> protocol logic to `os.apps.ssh_client`, not extending `_SshTool` in place.

- **C1. Implement `rt_io_tcp_connect` in the guest runtime**, mirroring the
  existing `rt_boot_tcp_*` server implementations in `baremetal_stubs.c`.
  *Est. 1–2 days. This is the only real blocker.*
- **C2. Swap `std.io.signature_sffi.verify_host_key` for
  `os.crypto.ed25519.ed25519_verify`** (+ the RSA/ECDSA equivalents already in
  `os.crypto`) in `_SshTool/run.spl:242` and `transport.spl:72`, removing the
  last SFFI edge from the client. *Est. 0.5 day.*
- **C3. Wire the shell entry:** `register_tools.spl:91` → call
  `os.tools.net.ssh_tool.run_ssh`. *Est. 1 hour.*
- **C4. Add client specs.** Coverage today is one describe block on
  `ssh_build_version_string`. Minimum: a loopback spec that runs `run_ssh`
  against the in-repo `sshd` (both are pure Simple in the same process space),
  plus a KEX/cipher/userauth transcript spec.
- **C5. `known_hosts` / TOFU pinning** — the client verifies the host-key
  *signature* but never checks the key is the *expected* key, so it is
  MITM-able today. Small, and should land with C2.
- **C6. Non-interactive `exec` mode** (`ssh host cmd`) — the client only opens
  an interactive shell.

Cleanup: delete the `ssh_sffi.spl` / `ssh_ffi.spl` facade and its `rt_ssh_*`
stubs. It is 1,536+ lines of API that can only ever return nil, and its presence
is what made the roadmap believe SSH depended on libssh2.

## Ledger change made

`doc/08_tracking/os/production_status.sdn`, the `ssh:` note line only. No source
was modified in this lane.
