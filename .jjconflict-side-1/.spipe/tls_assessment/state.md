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
| Certificate chain verification (issuer/subject, CA flag, anchor match) | implemented; was OFF BY DEFAULT when surveyed, **now unconditional** | `_CertVerify/signature_verify.spl:400-442`; was gated on a non-empty `root_store` with `tls13_default_client_config()` supplying `[]`; now driven by `_CertVerify/peer_policy.spl:57` — see §5 |
| **Hostname / SAN verification** | **WAS ABSENT repo-wide — added by this lane** | `_CertVerify/hostname_verify.spl`; see §4, and §5 for where it is now called from |
| Certificate validity period (notBefore/notAfter) | absent when surveyed, **CLOSED mid-session** | was zero hits across both trees; `_CertVerify/validity.spl` landed in a parallel session — see §5 |
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

### `os_tls_cert_chain_spec.spl` — red on the SEED, GREEN once the seed bug is worked around

`bin/simple test test/03_system/os/os_tls_cert_chain_spec.spl` (unpiped, full
capture, ~35 min under load):

```
Results: 4 total, 1 passed, 3 failed
  x parses leaf certificate pieces compatible with rsa_pss_sha256_verify
      unexpected verify_cert_chain failure: unsupported certificate signature algorithm
  x accepts a valid leaf -> intermediate chain anchored in the root store
  x rejects the chain when the trust anchor is absent
  v rejects an intermediate certificate that is not marked as a CA
```

**This is a SEED-PARSER artifact, not a TLS defect** (see §3), and the chain is
exact: the RSA-PSS
algorithm OID is `2a 86 48 86 f7 0d 01 01 0a`. With `_hex_digit("f") == 14`, the
`f7` byte decodes as `e7`, so `_is_rsa_pss_oid` never matches,
`_sig_scheme_from_algorithm_tlv` returns 0, and every signature check reports
"unsupported certificate signature algorithm".

Replacing this file's `_hex_digit` if-chain with a table lookup — **no other
change to the spec or to any source file** — takes the same command to:

```
Results: 4 total, 4 passed, 0 failed
```

That is the causal proof, and it clears `verify_cert_chain`: the TLS
chain-verification code was correct all along. In the 1/4 state the single
"passing" example was passing vacuously — "rejects an intermediate certificate
that is not marked as a CA" asserts only that a rejection occurs, and it got one
from the corrupted-OID path rather than the BasicConstraints check it names.

**MEASUREMENT TRAP — worth recording.** The first two attempts at this spec were
run as `timeout 900 bin/simple test ... | tail -25`. The harness reported **exit
code 0** and the captured output contained no `Results:` line, which reads like
"the spec produced no examples". It is nothing of the sort: in a pipeline the exit
status is `tail`'s, not `timeout`'s, so a `timeout`-killed run reports success.
Always run these unpiped. I nearly filed "produces zero examples" as a finding.

**Other pre-existing TLS specs: NOT run.** No verdict is claimed for
`os_tls_client_auth_spec`, `os_tls_diag_spec`, `os_tls_hosted_interop_basic_spec`,
the 12 `test/*/os/tls13/*_spec.spl` files, or
`tls12_record_handshake_round_trip_spec`. Do not read this document as evidence
that they pass. Any of them that copied the same `_hex_digit` helper should be
assumed affected until re-run.

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

## 3. Seed parser defect — REDISCOVERED, already filed, and my first framing was WRONG

I hit this while writing fixtures and initially wrote it up as "the last arm of a
long single-line `if`-chain returns the previous arm's value". **That framing is
wrong and a parallel lane (IFCHAIN) had already filed the correct one the same
day.** Recording the correction because the wrong diagnosis points at innocent
code:

- Bug: `doc/08_tracking/bug/if_chain_last_arm_returns_previous_value_2026-07-28.md`
- Gate spec: `test/01_unit/compiler/if_chain_arm_value_spec.spl`
- Root cause: `src/compiler_rust/parser/src/expressions/binary.rs:68-90` — the
  leading-operator line-continuation path peeks through NEWLINE/INDENT without
  comparing indentation.
- Real rule: **any** line beginning with `-` or `+` at the **same indent** as the
  previous statement is glued on as a *binary* operator. `if` is irrelevant, chain
  length is irrelevant. `return 15` ⏎ `-1` parses as `return (15 - 1)` = 14, and
  the function is left with no tail expression, so the fall-through returns **nil**.
- **Rust seed only.** The pure-Simple parser is correct. Everything I measured this
  session was on the seed (see the header note), which is why I saw it at all.

This also subsumes what I had written up as a second, separate defect: the
"reproducible core dump" on `build/tlsver_min.spl` is the *same* bug. The `-1`
sentinel is swallowed, the miss path returns nil, and `print "z={rz}"` on nil
aborts. One defect, not two.

### Consequence for the TLS specs — and the correction that matters

`os_tls_cert_chain_spec.spl` was **1/4 at HEAD on the seed** for exactly this
reason (RSA-PSS OID `2a 86 48 86 f7 0d ...`; `f7` decoded as `e7`). After
replacing its `_hex_digit` if-chain with a table lookup — **no other change** —
the same command reports:

```
Results: 4 total, 4 passed, 0 failed
```

So: **the three failures were a seed-parser artifact, NOT a defect in the TLS
chain-verification code.** `verify_cert_chain` is fine. Do not read the earlier
"red at HEAD" line as evidence against the TLS implementation; it was evidence
against the seed. What *is* a real (if now-moot) observation is that the single
example which passed at 1/4 passed vacuously — it asserts only that a rejection
occurs, and it got one from the corrupted-OID path rather than from the
BasicConstraints check it names.

25 files repo-wide carry the same `_hex_digit` shape, including the shared
`test/03_system/os/os_crypto_ref_helpers.spl` and several RSA/AES/Ed25519 KAT
specs. **This does not undermine the "crypto is KAT-verified" claim** — the defect
is seed-only, and those specs run correctly on the pure-Simple binary. I patched
only the one TLS spec I was measuring; the rest are IFCHAIN's call, and the proper
fix is the parser, not 25 copies of a workaround.

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

## 5. Residual risk — SUPERSEDED by a parallel lane, mid-session

When I wrote this I recorded that the fix hardened only callers supplying a root
store, because `tls13_default_client_config()` sets `root_store: []` and my check
sat under that gate — so the default client still verified nothing. I filed
"make verification the default" and "certificate validity period" as the next two
increments.

**Both landed while this lane was running, in a parallel session, and the result
is better than what I would have written.** Recording it so nobody re-does it:

- `src/os/tls13/_CertVerify/peer_policy.spl:57` now owns the whole policy:
  `verify_peer_certificate(chain, root_store, hostname, now_unix,
  insecure_disable_certificate_verification)` -> validity, then chain, then
  hostname.
- Verification is **unconditional**. An empty `root_store` is an explicit
  *error* ("an empty trust store is not a request to skip verification"), not a
  bypass. The single opt-out is
  `config.insecure_disable_certificate_verification`, checked at exactly one site.
- `src/os/tls13/_CertVerify/validity.spl` adds the notBefore/notAfter check that
  §1 lists as absent — that row is now stale in my favour.
- `_Tls13/handshake.spl:595-607` calls `verify_peer_certificate` and my earlier
  inline `verify_hostname` call there is gone.

**My work was adopted, not clobbered.** `peer_policy.spl:90` calls
`verify_hostname(chain[0], hostname)` — this lane's function — and carries my
RFC 6125 comment verbatim; `validity.spl:336` cites "the aliasing reason
documented in hostname_verify.spl". `src/os/tls13/_CertVerify/hostname_verify.spl`
is byte-identical to what this lane wrote (verified against the out-of-tree backup).

I deliberately did **not** restore my inline call at the old site. Re-adding it
would duplicate the check and partially revert their unconditional design — the
"origin already supersedes you" case in `.claude/rules/vcs.md`. Probe re-run
against the integrated tree: `TLSVER_FAILS=0`.

Still open after all of this:
1. RFC 8446 §4.1.3 downgrade-sentinel check on ServerHello.random — still absent.
2. Alert protocol — still absent; violations drop the socket with no alert.
3. Revocation (CRL/OCSP/stapling), KeyUsage/EKU/pathLen — still absent.
4. `src/os/tls12/` remains scaffolding with no verification of any kind.
5. The other pre-existing TLS specs still have no verdict (§2).

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
