# rsa_pss_typed_evidence_spec

Status: **AUTHORED_UNRUN**. Branch coverage: **UNMEASURED**.

Authored companion; admitted execution and zero-stub spipe-docgen generation remain pending.

Executable: `test/02_integration/lib/crypto/rsa_pss_typed_evidence_spec.spl`

Spec SHA-256: `b944466d503680f1b001f30f8d6a353bd39af06390c5733a2ae944326d35f73c`

Execution artifact SHA-256: absent. Proof class: production API assertions authored, not executed.

## Scenario flow

- REQ-TLS-RSAPSS-EVIDENCE-001: bind evidence to real verification
- should accept the independent encoding and compare a closed oracle
  - Load the independently produced encoded message
  - Verify through the production RSA-PSS API
  - Compare the observed verdict with the fixed expected verdict
- should reject a tampered message and fail an accepting oracle
  - Keep the independent encoding and replace the signed message
  - Prove the incorrect acceptance oracle fails closed
- should fail the acceptance oracle when verification evidence is missing
  - Present no verdict to the required-verdict oracle

<details><summary>Executable SSpec</summary>

```simple
"""
# RSA-PSS verification and fail-closed typed evidence
AUTHORED_UNRUN; coverage UNMEASURED. RFC 8017 section 9.1.2.
Uses the existing independent OpenSSL 3.0.13 / pyca 41.0.7 encoded-message
fixture, not an official NIST vector. This is the EMSA primitive integration,
not a TLS handshake or CertificateVerify transcript construction test.
"""
use std.spec.*
use std.spec.step
use std.common.crypto.rsa_pss.{rsa_pss_emsa_verify_sha256}
use std.common.spec.evidence.model.{EvidenceStatus, canonical_evidence, evidence_node, oracle_spec, check_exact}
use std.common.spec.evidence.evidence_comparator.{compare_evidence}
fn _hd(c: text) -> i64:
    if c == "0": return 0
    if c == "1": return 1
    if c == "2": return 2
    if c == "3": return 3
    if c == "4": return 4
    if c == "5": return 5
    if c == "6": return 6
    if c == "7": return 7
    if c == "8": return 8
    if c == "9": return 9
    if c == "a": return 10
    if c == "b": return 11
    if c == "c": return 12
    if c == "d": return 13
    if c == "e": return 14
    if c == "f": return 15
    -1

fn _hex(s: text) -> [u8]:
    var out: [u8] = []
    var i: u64 = 0
    while i < s.len():
        out.push((_hd(s[i]) * 16 + _hd(s[i + 1])).to_u8())
        i = i + 2
    out

fn _msg() -> [u8]:
    # "TLS 1.3, server CertificateVerify"
    _hex("544c5320312e332c20736572766572204365727469666963617465566572696679")

fn _em1024() -> text:
    "0e181bea22846d862682da2b43234fad753e58642f567c2be169f4575f13572a034b623890d0318370a3fb23a005f03a1567608bee03286764ae8ffd205704da3c634707642a86cf981bdae29e0495b4fe39e5c85830456ba1b5f265e63eff173ecda592cc9a7ad6f424886962c4db6dad5973296bc0cda07eaad06935608ebc"

fn pss_verdict_text(accepted: bool) -> text:
    if accepted: "accepted" else: "rejected"

describe "REQ-TLS-RSAPSS-EVIDENCE-001: bind evidence to real verification":
    it "should accept the independent encoding and compare a closed oracle":
        step("Load the independently produced encoded message")
        val encoding = _hex(_em1024())
        step("Verify through the production RSA-PSS API")
        val accepted = rsa_pss_emsa_verify_sha256(_msg(), encoding, 1023, 32)
        expect(accepted).to_equal(true)
        step("Compare the observed verdict with the fixed expected verdict")
        val evidence = canonical_evidence("protocol_text", "rsa-pss-verdict/1", [evidence_node("verification.status", pss_verdict_text(accepted))])
        val oracle = oracle_spec("rsa-pss-verdict/1", [check_exact("verification.status", "accepted")])
        expect(compare_evidence(evidence, oracle).status).to_equal(EvidenceStatus.passed)

    it "should reject a tampered message and fail an accepting oracle":
        step("Keep the independent encoding and replace the signed message")
        val accepted = rsa_pss_emsa_verify_sha256([0u8], _hex(_em1024()), 1023, 32)
        expect(accepted).to_equal(false)
        step("Prove the incorrect acceptance oracle fails closed")
        val evidence = canonical_evidence("protocol_text", "rsa-pss-verdict/1", [evidence_node("verification.status", pss_verdict_text(accepted))])
        val oracle = oracle_spec("rsa-pss-verdict/1", [check_exact("verification.status", "accepted")])
        expect(compare_evidence(evidence, oracle).status).to_equal(EvidenceStatus.failed)

    it "should fail the acceptance oracle when verification evidence is missing":
        step("Present no verdict to the required-verdict oracle")
        val evidence = canonical_evidence("protocol_text", "rsa-pss-verdict/1", [])
        val oracle = oracle_spec("rsa-pss-verdict/1", [check_exact("verification.status", "accepted")])
        expect(compare_evidence(evidence, oracle).status).to_equal(EvidenceStatus.failed)
```

</details>
