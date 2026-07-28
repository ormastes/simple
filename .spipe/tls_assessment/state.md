# Lane TLSVER — TLS stack assessment + hostname-verification fix

Date: 2026-07-28. Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
(NOTE: this binary prints `WARNING: this Rust-built Simple binary is a bootstrap
seed only` on every run — the deployed "release" binary is currently the SEED, not
the pure-Simple self-hosted tool. All verdicts below are SEED verdicts. That is a
standing violation of `.claude/rules/bootstrap.md` and belongs to the bootstrap lane.)

Machine was under load average ~75 with ~176 concurrent `simple` processes for the
whole session; the full-suite spec runs are correspondingly slow. Where a spec did
not finish, this document says so rather than guessing.

## 1. Inventory — what exists

### `src/os/tls13/` — 8,118 lines, the real TLS 1.3 implementation

| Capability | Status | Evidence |
|---|---|---|
| Record layer (plaintext + AEAD, seq numbers) | implemented | `record13.spl` (500), `_Tls13/context_io.spl:1-549` |
| Client handshake state machine (CH -> SH -> EE -> Cert -> CV -> Fin) | implemented | `_Tls13/handshake.spl:17-780`, message loop at `:347-540` |
| Server handshake | implemented | `server_handshake.spl` (607), `server.spl`, `server_builders.spl` |
| Key schedule / HKDF | implemented | `key_schedule.spl` (393), `hkdf.spl` (412) |
| Transcript hash | implemented | `transcript.spl` (55) |
| HelloRetryRequest | implemented | `handshake13_hrr.spl` (452), `tls13_connect_hrr_p256.spl` |
| KeyUpdate (post-handshake) | implemented | `key_update.spl` (157), `tls13_key_update.spl` (134) |
| NewSessionTicket / PSK / 0-RTT | implemented | `new_session_ticket.spl` (337), `psk.spl` (349), `_Tls13/psk_connect.spl` |
| Extension builders (SNI, supported_versions, ALPN, sig_algs, groups) | implemented | `handshake13_ext_builders.spl` (239) |
| CertificateVerify signature verify (Ed25519 / RSA-PSS / ECDSA P-256/384/521) | implemented | `_CertVerify/signature_verify.spl:1-379`, `_CertVerify/der_parsing.spl` |
| Certificate chain verification (issuer/subject, CA flag, anchor match) | implemented **but OFF BY DEFAULT** | `_CertVerify/signature_verify.spl:400-442`; only caller is `_Tls13/handshake.spl:587`, gated on `config.root_store.len() > 0`, and `tls13_default_client_config()` sets `root_store: []` (`_Tls13/psk_connect.spl:294-309`) |
| **Hostname / SAN verification** | **WAS ABSENT — added by this lane** | see §4 |
| Certificate validity period (notBefore/notAfter) | **absent** | zero hits for `not_after`/`not_before`/`expir` across `src/os/tls13/**` and `src/os/tls12/**` |
| Revocation (CRL / OCSP / stapling) | absent | no matches |
| KeyUsage / ExtendedKeyUsage / pathLenConstraint enforcement | absent | `_extract_is_ca` (`der_parsing.spl:520`) reads BasicConstraints.cA only |
| Alert protocol (send/receive, fatal alerts on violation) | **absent** | zero hits for `send_alert`/`fatal_alert`/`alert(` in either tree; protocol violations return `Tls13ConnectResult.Failed` and drop the socket without an alert |
| Downgrade-sentinel check (RFC 8446 §4.1.3 `DOWNGRD` in ServerHello.random) | **absent** | zero hits for `downgrade`/`DOWNGRD` |
| Cipher suites | AES-128/256-GCM-SHA256/384 + ChaCha20-Poly1305 | specs `aes256_gcm_sha384_cipher_suite_spec.spl`, `chacha20_poly1305_cipher_suite_spec.spl` |

### `src/os/tls12/` — 848 lines
`tls12_record.spl` (160), `tls12_handshake.spl` (456), `tls12_extensions.spl` (199).
Message construction/parsing only. No chain verification, no hostname verification,
no alerts, no downgrade protection. Treat as protocol scaffolding, not a usable client.

### `src/lib/*/tls/` — NOT duplicated (a good finding)
The earlier concern about shadowed byte-identical tiers does **not** apply here.
There is exactly one implementation, `src/lib/nogc_sync_mut/tls/` (63,357 bytes,
8 files), and the other tiers are thin `export use` re-export facades:
`gc_sync_mut/tls/*` 206-224 bytes each, `gc_async_mut/tls/*` and
`nogc_async_mut/tls/*` 122-1,664 bytes each (e.g.
`src/lib/gc_async_mut/tls/handshake.spl` is a single `export use
std.nogc_async_mut.tls.handshake.{...}` line). `nogc_async_mut/tls/ech.spl`
(10,281 bytes) is real code unique to that tier.
Separately, `src/lib/nogc_async_mut_noalloc/tls/` (12 files) is an independent
baremetal client — that IS a second implementation, but a deliberate one for the
no-alloc tier, not an accidental shadow.
Note this lib tree is TLS **1.2**-shaped (`build_client_key_exchange_hex`); the
1.3 work lives in `src/os/tls13/`. Two protocol generations, two owners.

## 2. Spec verdicts

Owned/new spec, run via a fast standalone driver (`build/tlsver_probe.spl`,
`bin/simple run`, same oracles as the spec file):

| describe | verdict |
|---|---|
| `extract_san_dns_names` | 5/5 pass |
| `dns_name_matches` | 15/15 pass |
| `verify_hostname` | 16/16 pass |
| total | **36 checks, 0 failures** (`TLSVER_FAILS=0`) |

The spec file itself also completed through the real runner:
`bin/simple test test/03_system/os/os_tls_hostname_verify_spec.spl` ->
**`Results: 9 total, 9 passed, 0 failed`** (9 `it` blocks across the 4 describes).

Deliberate-red calibration (two mutants applied together, then reverted):
1. `p_labels.len() < 3` -> `< 2` (allow `*.com`)
2. the no-SAN branch returns `CertVerifyResult.Ok` (fail open)

Result: exactly 3 assertions went red — `*.com public suffix`, `no-SAN cert w/
matching CN rejected`, `empty cert rejected` — and nothing else. Reverted; re-ran;
`TLSVER_FAILS=0`. The specs discriminate.

**Pre-existing TLS specs: NOT re-verified.** `bin/simple test
test/03_system/os/os_tls_cert_chain_spec.spl` was started twice and did not produce
a `Results:` line within 600s under the session load. No verdict is claimed for
`os_tls_cert_chain_spec`, `os_tls_client_auth_spec`, `os_tls_diag_spec`,
`os_tls_hosted_interop_basic_spec`, the 12 `test/*/os/tls13/*_spec.spl` files, or
`tls12_record_handshake_round_trip_spec`. Do not read this document as evidence
that they pass.

**A/B engine note:** the probe was run twice — default engine and
`SIMPLE_EXECUTION_MODE=interpreter` — and both report `TLSVER_FAILS=0`,
`san_count=3`. **But I cannot prove the two runs used different engines.** The
control I used to detect a switch (compiler defect (a) below) reproduces
*identically* under both settings (`hd("f")=14` either way), which is consistent
with a shared front-end/HIR and equally consistent with the env var being ignored
by this binary. Read the A/B as "no divergence observed", not as "both engines
verified". The module deliberately avoids the known divergence surfaces (no
`Dict`, no `Option`, no `+=`, no struct-field mutation, no defaulted struct
fields), but that is an argument, not a measurement.

## 3. Compiler defects found while building this (NOT fixed here — off-lane)

**(a) Last arm of a long single-line `if`-chain returns the previous arm's value.**
```
fn hd(c: text) -> i64:
    if c == "0": return 0
    ... 15 more ...
    if c == "f": return 15
    -1
```
`hd("f")` returns **14**, not 15. `hd("e")`=14, `hd("a")`=10, `hd("9")`=9 are all
correct — only the final arm is wrong. Confirmed directly on `bin/simple run`.

Impact beyond this lane: **`test/03_system/os/os_tls_cert_chain_spec.spl:22-40`,
`test/system/os_tls_cert_chain_spec.spl`, and every sibling spec that copied this
`_hex_digit` helper decode every `f` nibble as `e`.** Their embedded RSA
certificate fixtures are therefore corrupt in memory. Whatever those specs report,
they are not exercising the certificates their authors wrote down. This should be
re-checked by whoever owns those specs once the compiler defect is fixed.
Workaround used here: table lookup over `"0123456789abcdef"` (see
`test/03_system/os/os_tls_hostname_verify_spec.spl:28` and
`build/tlsver_probe.spl:13`).

**(b) Reproducible core dump.** `build/tlsver_min.spl` (12 lines: a 3-arm
single-line `if`-chain plus `main`) makes `bin/simple run` dump core, twice in a
row, while larger files in the same directory run fine.

Both belong to the compiler lane; `src/compiler/**` is out of scope for TLSVER.

## 4. The fix — RFC 6125 hostname verification

New: `src/os/tls13/_CertVerify/hostname_verify.spl` (~270 lines).
Exported via `src/os/tls13/cert_verify.spl:29`.
Wired at `src/os/tls13/_Tls13/handshake.spl:590-596`, immediately after the chain
check and under the same `config.root_store.len() > 0` gate.

- `extract_san_dns_names(cert_der) -> [[u8]]` — walks the TBS extensions for OID
  2.5.29.17, parses the GeneralNames SEQUENCE, collects tag `0x82` (dNSName),
  ASCII-folds to lowercase. IP SANs (`0x87`) are deliberately not collected.
- `dns_name_matches(pattern, host) -> bool` — exact match, or a wildcard that must
  be the whole leftmost label, with the presented name required to have >= 3
  labels. Rejects `*.com`, `w*.example.com`, `www.*.example.com`, and any name with
  an empty label or a byte outside 0x21-0x7E.
- `verify_hostname(cert_der, hostname) -> CertVerifyResult` — fails closed on an
  empty/non-ASCII reference name, an absent SAN, a SAN with no dNSName, and an
  unparsable certificate.

**Subject CN is deliberately NOT a fallback** (RFC 6125 §6.4.4). The repo's own
existing fixtures are CN-only with no SAN, so a CN fallback would have made the
specs easier and the code wrong.

Two implementation notes worth keeping:
- SAN entries are cut with `_hv_fold_slice` / `_hv_slice`, which are *functions*
  returning fresh arrays. An earlier draft accumulated into a `var` declared inside
  the loop body; the specs are written to catch that class of aliasing.
- The SAN OID is located by byte scan (matching the existing `_extract_is_ca`
  approach). A candidate that fails to parse does not abort the scan, and every
  failure path leaves the name list empty, so a random OID collision inside a
  modulus degrades to a verification *failure*, never a bypass.

## 4b. Lint

`bin/simple lint src/os/tls13/_CertVerify/hostname_verify.spl` reports 11 errors,
all `COLL006 "string concat in loop"`. Every one is a false positive fired on
`out.push(...)` into a `[u8]` / `[[u8]]` accumulator — there is no text
concatenation in the file. Baseline for comparison: the pre-existing sibling
`src/os/tls13/_CertVerify/der_parsing.spl` reports **25** errors of the same kind,
and `test/03_system/os/os_tls_cert_chain_spec.spl` reports 1. The rule is
mis-firing on byte arrays across this whole tree; the code was not distorted to
satisfy it. `COLL006` on `[u8]` accumulation is worth a lint-lane bug.

## 5. Honest residual risk

The fix closes hostname verification **only for callers that supply a root store**.
`tls13_connect(fd, hostname)` still uses `tls13_default_client_config()`, whose
`root_store` is `[]`, so the default client performs **no chain verification and no
hostname verification** — it authenticates only that the peer holds the key for
whatever certificate it sent. That is still trivially MITM-able. Flipping the
default is a behaviour change that would break the existing CN-only fixtures and
every in-repo caller, so it is filed as the next increment, not smuggled in here.

Next increments, in priority order:
1. Make verification the default: a `verify_peer: bool` on `Tls13ClientConfig`
   defaulting to true, with an explicit opt-out for the self-signed test fixtures.
2. Certificate validity period (notBefore/notAfter) — currently absent entirely.
3. RFC 8446 §4.1.3 downgrade-sentinel check on ServerHello.random.
4. Alert protocol: send a fatal alert on protocol violation instead of silently
   dropping the connection.
5. Re-verify the cert-chain specs once compiler defect (a) is fixed.

## 6. Lean — `src/verification/tls_isolation/`

`lake build` exits **0**, "Build completed successfully (3 jobs)", no `sorry`
(the only occurrence of the word is a comment at `src/TlsIsolation.lean:18`
asserting there are none), `TlsIsolation.olean` produced.

**It has nothing to do with Transport Layer Security.** "TLS" here means
*thread-local storage*. The file defines `structure TlsStore`, `tlsWrite`,
`tlsRead` over `ThreadId`/`Key`/`Value`, and proves 4 theorems: `tls_read_own`,
`tls_thread_isolated`, `tls_key_isolated`, `tls_writes_commute`. Zero TLS-protocol
content. Any roadmap entry that counts this as formal verification of the TLS stack
is miscounting. There is **no** formal model of the TLS protocol in this repo.

## Files

- `src/os/tls13/_CertVerify/hostname_verify.spl` — new, the fix
- `src/os/tls13/cert_verify.spl` — export line added
- `src/os/tls13/_Tls13/handshake.spl` — verification wired into connect
- `test/03_system/os/os_tls_hostname_verify_spec.spl` — new spec, 4 describes
- `build/tlsver_probe.spl` — fast standalone driver (36 checks)
- `build/tlsver_min.spl`, `build/tlsver_hx.spl` — compiler-defect repros
- `doc/08_tracking/os/production_status.sdn` — new `tls:` row
