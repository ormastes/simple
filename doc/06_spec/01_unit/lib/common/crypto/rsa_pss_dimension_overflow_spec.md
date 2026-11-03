# RSA-PSS dimension overflow regression

Status: **AUTHORED_UNRUN**. Branch coverage: **UNMEASURED**.

Authored companion, not generated or executed evidence. RFC 8017 section 9.1.2, printed pages 44–45.

Executable: `test/01_unit/lib/common/crypto/rsa_pss_dimension_overflow_spec.spl`

Spec SHA-256: `333efbae9a5cc3143cef6d938f0de7030975dbfc07a9e08d4c9d9e5c355de66b`

Execution artifact SHA-256: absent. Proof class: production API regression authored; source-discovered overflow risk.

## Scenario flow

- REQ-TLS-RSAPSS-DIMENSION-001: arithmetic-safe dimension rejection
- should reject the largest signed bit length without rounding overflow
  - Submit an impossible bit length to the production EMSA verifier
- should reject the largest salt before accessing an empty encoding
  - Submit a salt length whose additive size check would overflow
- should reject an overflowing salt with correctly sized nonempty framing
  - Keep encoded length consistent while salt exceeds available space
- should reject the minimum signed bit length before computing encoded size
  - Submit a negative bit count to the production EMSA verifier

<details><summary>Executable SSpec</summary>

```simple
"""
# RSA-PSS dimension arithmetic rejects unrepresentable inputs
REQ-TLS-RSAPSS-DIMENSION-001. RFC 8017 section 9.1.2, printed pages 44–45:
the encoding must have room for the hash, salt, delimiter and trailer.
Host integer arithmetic must reject impossible dimensions without overflowing.
AUTHORED_UNRUN / UNMEASURED; no native execution or branch coverage claim.
"""
use std.spec.*
use std.spec.step
use std.common.crypto.rsa_pss.{rsa_pss_emsa_verify_sha256}

fn rsa_pss_dimension_minimum_em() -> [u8]:
    var encoding: [u8] = []
    var i: i64 = 0
    while i < 33:
        encoding.push(0u8)
        i = i + 1
    encoding.push(188u8)
    encoding

describe "REQ-TLS-RSAPSS-DIMENSION-001: arithmetic-safe dimension rejection":
    it "should reject the largest signed bit length without rounding overflow":
        step("Submit an impossible bit length to the production EMSA verifier")
        expect(rsa_pss_emsa_verify_sha256([], [], 9223372036854775807, 0)).to_equal(false)

    it "should reject the largest salt before accessing an empty encoding":
        step("Submit a salt length whose additive size check would overflow")
        expect(rsa_pss_emsa_verify_sha256([], [], 0, 9223372036854775807)).to_equal(false)

    it "should reject an overflowing salt with correctly sized nonempty framing":
        step("Keep encoded length consistent while salt exceeds available space")
        expect(rsa_pss_emsa_verify_sha256([], rsa_pss_dimension_minimum_em(), 272, 9223372036854775807)).to_equal(false)

    it "should reject the minimum signed bit length before computing encoded size":
        step("Submit a negative bit count to the production EMSA verifier")
        expect(rsa_pss_emsa_verify_sha256([], [], -9223372036854775807 - 1, 0)).to_equal(false)
```

</details>
