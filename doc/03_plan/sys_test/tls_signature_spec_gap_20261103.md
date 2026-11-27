# TLS signature and key-agreement specification gaps

Status: **AUTHORED_UNRUN / UNMEASURED**. Target is 99% measured branch coverage
per production owner/backend, not scenario count. No admitted runtime was used,
no numerator or denominator was measured, and no requirement is marked complete.

## Scope and existing evidence

The common production owners are `src/lib/common/crypto/rsa_pss.spl`,
`ecdsa_p256.spl`, and `ecdh_p256.spl`. RSA-PSS and ECDH are pure Simple;
ECDSA delegates through the checked signature SFFI. Coverage of a foreign
ECDSA implementation must not be presented as Simple wrapper coverage.

Existing executable evidence, not claimed run this session:

- `test/01_unit/lib/crypto/rsa_pss_verify_openssl_kat_spec.spl`: independent
  OpenSSL EMSA and full RSA signatures, altered message/signature, salt mismatch.
  These are OpenSSL-produced fixtures, not published NIST vectors.
- `test/01_unit/lib/common/crypto/ecdsa_p256_spec.spl`: NIST CAVP verification
  and signer round trips. Its helper bypasses the common verifier because of a
  recorded bare-name resolution collision. New framing checks import that
  verifier with an alias; native symbol binding still needs verification.
- `test/01_unit/lib/crypto/p256_ecdh_nist_cdh_kat_spec.spl`: NIST CDH public key,
  shared secret, invalid point/X encoding, zero/order scalars, DH symmetry.

TLS version boundary: RFC 8446 signature algorithms authenticate TLS 1.3;
RSA key transport is not a TLS 1.3 key exchange. This lane does not establish
full TLS CertificateVerify transcript construction or a handshake. ECDSA's
common API takes fixed-width r||s, whereas TLS ECDSA signatures use DER.
P-384/P-521 support and unimplemented algorithms are not inferred from P-256.

## Added traceability

| Requirement | Rule | Executable (relative to test/) | Cases |
|---|---|---|---:|
| REQ-TLS-RSAPSS-BOUNDARY-001 | RFC 8017 §9.1.2 pp. 44–45 dimensions and minimum encoded size | 01_unit/lib/common/crypto/signature_spec_boundaries_spec.spl | 3 |
| REQ-TLS-RSAPSS-BOUNDARY-002 | RFC 8017 §8.1.2 pp. 34–35 signature width and representative range; zero-modulus API rejection | 01_unit/lib/common/crypto/signature_spec_boundaries_spec.spl | 3 |
| REQ-TLS-ECDSA-BOUNDARY-001 | Existing common API signature/SPKI framing errors | 01_unit/lib/common/crypto/signature_spec_boundaries_spec.spl | 3 |
| REQ-TLS-ECDH-BOUNDARY-001 | RFC 8446 §4.2.8.2 p. 51 point validation plus existing scalar contract | 01_unit/lib/common/crypto/p256_key_parameter_boundaries_spec.spl | 3 |
| REQ-TLS-RSAPSS-EVIDENCE-001 | Production verification verdict, fixed positive oracle, tampered input and missing evidence rejection | 02_integration/lib/crypto/rsa_pss_typed_evidence_spec.spl | 3 |

Manuals mirror each executable under `doc/06_spec/`, replacing `.spl` with
`.md`. They contain visible steps, folded source, source SHA-256, and explicit
absence of execution-artifact hashes. They are authored companions, not
generated PASS evidence. Page numbers above are printed pages in the official RFC Editor TXT editions,
pinned by the campaign specification-document owner. RFC 8017 TXT SHA-256:
`1e72dc473d18df3fc5598cdc12795a9f18f36f1aef15abc23a55eb0d58151d11`.
Official sources: https://www.rfc-editor.org/rfc/rfc8017.txt and
https://www.rfc-editor.org/rfc/rfc8446.txt. These RFC text sources are not
represented as original official PDFs.

## Execution and acceptance

Run each changed spec once with the admitted source-matched native test runner,
preserving binary and producer hashes, actual test counts and failure details.
Require all cases to execute; alias-resolution or missing SFFI errors are
blockers, not reasons to replace the production API with a copied test helper.
Then run admitted `spipe-docgen` for each spec and require zero stubs.

The coverage coordinator owns actual branch collection. Include zero-hit
branches and report each owner's numerator/denominator separately. These
boundary additions do not claim 99%, full FIPS 186-5 compliance, wrong-key
coverage completeness, all signature schemes, or TLS integration completeness.
X25519/RFC 7748 remains a separate worker's lane.

Manual policy: primary steps visible, source folded, no captures invented.
Integration evidence is an in-process production verdict with a closed typed
oracle; the no-node case deliberately checks the comparator's fail-closed path.
Agent ownership: signature/key-parameter tests worker; root merge owner;
Astra phase-3 reviewer. No source changes or bootstrap work authorized here.
