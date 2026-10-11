# SimpleOS embedded TLS material specification

Offline embedded-material and TLS 1.3 handshake-message diagnostics for
`REQ-SSPEC-SYSTEM`. This spec does not perform a live TLS handshake.

| Field | State |
|---|---|
| Canonical source | `test/03_system/os/simpleos_tls_embedded_material_spec.spl` |
| Scenarios | 3 |
| Runtime | **Focused Phase 1 diagnostic PASS — 3/3, cycle one** |
| Coverage | 80% owner annotations are targets, not measured coverage |
| Manual generation | Exact source transcription; self-hosted docgen pending |

Cycle one completed with **3 passed, 0 failed, 0 skipped and 0 dropped** in
**4776 ms**, process exit **0**. The resource receipt records peak process-tree
RSS **251764 KiB**, enforced limit **5859375 KiB**, and **quiescent=1**.
The coordinator verified the pinned 174-source-file closure and seed hashes
before and after execution. No passing case was rerun.

Evidence: [`cycle-one.log`](../../../../build/phase-one-storage-gui-diagnostic/simpleos_tls_embedded_material_spec/cycle-one.log),
[`cycle-one.rss.env`](../../../../build/phase-one-storage-gui-diagnostic/simpleos_tls_embedded_material_spec/cycle-one.rss.env),
[`cycle-one.exit`](../../../../build/phase-one-storage-gui-diagnostic/simpleos_tls_embedded_material_spec/cycle-one.exit),
and [`tls-material-cycle-one-inputs.sdn`](../../../../build/phase-one-storage-gui-diagnostic/tls-material-cycle-one-inputs.sdn).

This result applies to the exact source embedded below and the admitted Phase 1
seed. Signing used the builder's existing `rt_ed25519_sign`; verification used
the production pure-Simple verifier. Native qualification, a live handshake,
measured coverage and self-hosted docgen remain unverified. The resource and
failure policy below remains the admission policy; its one diagnostic has
now completed successfully.

| Scenario | Production evidence |
|---|---|
| Certificate framing and material | The Certificate builder emits exact message/list/entry lengths and empty context/extensions; the production parser recovers every embedded DER byte. |
| Valid and changed-transcript CertificateVerify | The production parser extracts the algorithm/signature; the public key comes from the embedded certificate; the pure-Simple verifier accepts the signature and rejects it after one transcript byte changes. |
| Invalid signing inputs | The actual builder returns no message for an empty PKCS8 key and for an unsupported signature scheme. |

All message indexing is guarded by exact buffer lengths. Production parser
calls also require the asserted length fields to match, so nonfatal matchers
cannot admit malformed framing to a dependent parse. Public-key, signature
and transcript lengths guard dependent verification and mutation. Verification
failure is recorded rather than converted to a passing length assertion.

Production ownership is `src/os/kernel/net/embedded_certs.spl`,
`src/os/tls13/server_builders.spl`, `src/os/tls13/handshake13.spl`,
`src/os/tls13/_CertVerify/signature_verify.spl` and
`src/os/crypto/ed25519.spl`. The cert-verification facade also imports DER
helpers and ECDSA/RSA verification dependencies. This closure is larger than
the former message-length check.

The CertificateVerify builder retains its existing `rt_ed25519_sign` runtime
extern. Signature validation calls `verify_certificate_verify_msg_scheme`,
which uses the production pure-Simple Ed25519 verifier. No native verifier
shortcut or test implementation is substituted. The passing Phase 1 seed
diagnostic is therefore mixed-path evidence for these exact inputs;
it does not qualify the native runtime, baremetal entropy, network I/O,
key exchange, certificate-chain trust/validity/hostname policy, or a complete
TLS handshake. The certificate's own self-signature is not verified here.

The coordinator may run one admitted Phase 1 diagnostic with a 180-second,
5.6-GiB limit. Unavailable signing ABI, cryptographic rejection, resource
failure or missing runtime must remain recorded as failure/blockage, without
an alternate verifier or fabricated pass. Native and self-hosted evidence
remains open until an eligible runtime executes it.

The removed `test/system/simpleos_tls_embedded_material_spec.spl` had exactly
the same executable source as the old canonical file. Their sole difference
was the canonical file's first-line, incorrect debug-owner `@cover ... 0%`
annotation. Legacy SHA-256: `b185514bd44a1a6269416f3dce4f4834eb359d9758efddf59c4519fba2315323`.
The original real message-building intent is preserved and strengthened.
No previous execution result is inferred from this source repair.

Source SHA-256: `4afd9059fc773be6649515d326a4afe3198bd186a7741d005778c4f01916e41c`.

```simple
# Purpose and audience: embedded TLS material and handshake-message diagnostics for SimpleOS maintainers.
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/os/kernel/net/embedded_certs.spl 80%
# @cover src/os/tls13/server_builders.spl 80%
# @cover src/os/tls13/handshake13.spl 80%
# @cover src/os/tls13/_CertVerify/signature_verify.spl 80%
# @cover src/os/crypto/ed25519.spl 80%
# Coverage percentages are targets, not measured coverage.
# @tag:system
# Offline material/message evidence; no live handshake or native qualification.
# CertificateVerify signing uses the builder's existing rt_ed25519_sign extern;
# verification uses the production pure-Simple verifier, without an FFI substitute.

use std.spec.{describe, it, expect, fail, step}
use os.kernel.net.embedded_certs.{get_embedded_cert_der, get_embedded_key_der, has_embedded_certs}
use os.tls13.server_builders.{build_certificate, build_certificate_verify}
use os.tls13.handshake13.{parse_certificate_chain_body, parse_certificate_verify}
use os.tls13.cert_verify.{extract_ed25519_pubkey_from_cert, verify_certificate_verify_msg_scheme, CertVerifyResult}

fn _transcript_hash_32() -> [u8]:
    var h: [u8] = []
    var i: u64 = 0
    while i < 32u64:
        h.push(i.to_u8())
        i = i + 1u64
    h

# Copy the handshake body for the production parsers; this does not parse it.
fn _tls_material_body(message: [u8]) -> [u8]:
    var body: [u8] = []
    var i: u64 = 4
    while i < message.len():
        body.push(message[i])
        i = i + 1
    body

describe "SimpleOS embedded TLS material":
    it "frames the complete embedded DER certificate with empty request context and extensions":
        step("Load the embedded certificate and encode a server Certificate message")
        val cert_der = get_embedded_cert_der()
        expect(has_embedded_certs()).to_equal(true)
        expect(cert_der.len()).to_equal(317)
        expect(get_embedded_key_der().len()).to_equal(48)
        val message = build_certificate([cert_der])
        expect(message.len()).to_equal(330)
        if message.len() == 330:
            expect(message[0]).to_equal(0x0Bu8)
            expect(message[1]).to_equal(0u8)
            expect(message[2]).to_equal(1u8)
            expect(message[3]).to_equal(70u8)  # handshake body: 326 bytes
            expect(message[4]).to_equal(0u8)   # empty request context
            expect(message[5]).to_equal(0u8)
            expect(message[6]).to_equal(1u8)
            expect(message[7]).to_equal(66u8)  # certificate list: 322 bytes
            expect(message[8]).to_equal(0u8)
            expect(message[9]).to_equal(1u8)
            expect(message[10]).to_equal(61u8) # certificate DER: 317 bytes
            expect(message[328]).to_equal(0u8)
            expect(message[329]).to_equal(0u8)
            if message[4] == 0u8 and message[5] == 0u8 and message[6] == 1u8 and
               message[7] == 66u8 and message[8] == 0u8 and message[9] == 1u8 and
               message[10] == 61u8 and message[328] == 0u8 and message[329] == 0u8:
                step("Decode the certificate list and compare every DER byte")
                val chain = parse_certificate_chain_body(_tls_material_body(message))
                expect(chain.len()).to_equal(1)
                if chain.len() == 1:
                    expect(chain[0]).to_equal(cert_der)

    it "verifies the embedded key signature and rejects a changed transcript":
        step("Sign a transcript and inspect the complete CertificateVerify framing")
        val transcript = _transcript_hash_32()
        val message = build_certificate_verify(transcript, get_embedded_key_der(), 0x0807u16)
        expect(message.len()).to_equal(72)
        if message.len() == 72:
            expect(message[0]).to_equal(0x0Fu8)
            expect(message[1]).to_equal(0u8)
            expect(message[2]).to_equal(0u8)
            expect(message[3]).to_equal(68u8)
            expect(message[4]).to_equal(8u8)
            expect(message[5]).to_equal(7u8)
            expect(message[6]).to_equal(0u8)
            expect(message[7]).to_equal(64u8)
            if message[4] == 8u8 and message[5] == 7u8 and
               message[6] == 0u8 and message[7] == 64u8:
                val fields = parse_certificate_verify(_tls_material_body(message))
                expect(fields.algorithm).to_equal(0x0807u16)
                expect(fields.signature.len()).to_equal(64)
                val cert_der = get_embedded_cert_der()
                expect(cert_der.len()).to_equal(317)
                if cert_der.len() == 317:
                    val public_key = extract_ed25519_pubkey_from_cert(cert_der)
                    expect(public_key.len()).to_equal(32)
                    if public_key.len() == 32 and fields.signature.len() == 64:
                        step("Verify against the certificate public key using the production verifier")
                        match verify_certificate_verify_msg_scheme(public_key, fields.algorithm, transcript, fields.signature):
                            CertVerifyResult.Ok: pass
                            CertVerifyResult.Err(reason): fail("embedded CertificateVerify rejected: {reason}")
                        var changed = transcript
                        expect(changed.len()).to_equal(32)
                        if changed.len() == 32:
                            changed[0] = 255u8
                            step("Reject the same signature after changing one transcript byte")
                            match verify_certificate_verify_msg_scheme(public_key, fields.algorithm, changed, fields.signature):
                                CertVerifyResult.Ok: fail("changed transcript retained a valid signature")
                                CertVerifyResult.Err(_): pass

    it "rejects malformed signing material and unsupported signature schemes":
        step("Reject an empty PKCS8 key instead of emitting a signature-shaped message")
        expect(build_certificate_verify(_transcript_hash_32(), [], 0x0807u16)).to_equal([])
        step("Reject an unsupported scheme with otherwise valid embedded material")
        expect(build_certificate_verify(_transcript_hash_32(), get_embedded_key_der(), 0u16)).to_equal([])
```
