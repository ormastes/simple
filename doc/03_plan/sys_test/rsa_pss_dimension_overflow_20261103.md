# RSA-PSS untrusted dimension arithmetic

Status: **AUTHORED_UNRUN / UNMEASURED**. This is a source-discovered defect
and bounded repair, not an executed RED/GREEN receipt.

Owner: `src/lib/common/crypto/rsa_pss.spl`,
`rsa_pss_emsa_verify_sha256`. The public API accepts signed bit and salt
lengths. The original `(em_bits + 7) / 8` overflows for the maximum i64 bit
count. The original `32 + salt_len + 2` overflows for a maximum i64 salt.
Depending on backend overflow semantics, this can trap or bypass the size
check and reach invalid encoding accesses; no backend behavior is claimed
observed in this session.

REQ-TLS-RSAPSS-DIMENSION-001 maps to RFC 8017 §9.1.2, printed pages 44–45,
especially its encoded-length precondition. Official source:
https://www.rfc-editor.org/rfc/rfc8017.txt; pinned TXT SHA-256
`1e72dc473d18df3fc5598cdc12795a9f18f36f1aef15abc23a55eb0d58151d11`.
The requirement extends that mathematical bound to this API's finite-width
host integers; RFC 8017 does not specify a host language overflow policy.

Repair: reject nonpositive bit lengths, use `(em_bits - 1) / 8 + 1`, reject
encoded lengths below the fixed 34-byte overhead, then compare salt against
remaining space. All subtractions occur after their lower bound is checked.
Successful valid-size verification and the trailer/hash logic are unchanged.

Regression: `test/01_unit/lib/common/crypto/rsa_pss_dimension_overflow_spec.spl`
contains four actual production API calls: maximum bit length, minimum bit
length, maximum salt with empty encoding, and maximum salt with 34-byte
consistent framing. The last case reaches the salt-space guard independently
of invalid bit-length rejection. Existing known-answer and tamper scenarios
remain in `test/01_unit/lib/crypto/rsa_pss_verify_openssl_kat_spec.spl`.

Manual: `doc/06_spec/01_unit/lib/common/crypto/rsa_pss_dimension_overflow_spec.md`.
Source hash is present; execution-artifact hash is absent. No runtime was
admitted by the campaign coordinator, so native regression, original-versus-
fixed execution, core/library/MCP checks, native smoke, branch measurement,
and zero-stub spipe-docgen generation remain pending. No seed or bootstrap
fallback was used. This patch has no measured 99% coverage claim.

Acceptance requires the four scenarios to execute and reject cleanly, existing
independent RSA-PSS known answers to remain accepted, required core smoke to
complete, and measured branch counts to be reported by owner/backend. Parent
integration owns landing; Astra owns exact-commit source review.
