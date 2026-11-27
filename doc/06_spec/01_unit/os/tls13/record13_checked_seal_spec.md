# Checked TLS record sealing

Source: [record13_checked_seal_spec.spl](../../../../../test/01_unit/os/tls13/record13_checked_seal_spec.spl).
Requirement: REQ-TLS-CHECKED-SEAL-001.

Status: **AUTHORED_UNRUN**. Seventeen scenarios were authored before implementation;
no baseline RED or patched GREEN was executed. This is not completed TDD.

| Scenarios | Expected observation |
|---|---|
| AES-128 key lengths 0, 15, 17; ChaCha key lengths 0, 31, 33 | Explicit key-shape error before provider invocation |
| IV lengths 0, 11, 13 for each suite | Explicit IV-shape error before nonce derivation |
| AES-128 and ChaCha valid binary plaintext | Checked result equals unchanged legacy wire bytes; 26-byte record |
| Suites 0 and 0x1302 | Unsupported-suite error instead of implicit AES fallback |
| 16,385-byte plaintext | Explicit oversize error before record construction |

RFC 8446 sections 5.1–5.3 define record framing/nonce context; RFC 8439
section 2.8 defines ChaCha input widths. Error strings are repository contracts.
Valid controls test compatibility, not independent cryptographic correctness.
No provider-output-error branch coverage, native execution or security assurance
is claimed. Existing independent RFC core vectors remain separate.
