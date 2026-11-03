# Curve448 field boundary scenarios

**Status: AUTHORED_UNRUN.** This is an authored manual, not generated execution evidence. No admitted Simple runtime was available; SSpec, docgen, scorer, and branch instrumentation have not run. The existing X448 KAT mismatch remains OPEN.

Executable: [curve448_field_boundaries_spec.spl](../../../../../test/01_unit/lib/crypto/curve448_field_boundaries_spec.spl).

RFC 7748 section 4.2 defines p = 2^448 - 2^224 - 1. In radix 2^28, limb 8 of p is 0xFFFFFFE; the other limbs are 0xFFFFFFF. Section 5 requires field arithmetic modulo p.

| Requirement | Scenario | Exact oracle |
|---|---|---|
| REQ-CRYPTO-X448-001 | Subtract zero from zero | Sixteen zero limbs |
| REQ-CRYPTO-X448-001 | Subtract one from zero | Canonical p-1; limbs 0 and 8 are 0xFFFFFFE |
| REQ-CRYPTO-X448-002 | Reduce exactly p | Sixteen zero limbs, including top limb |
| REQ-CRYPTO-X448-002 | Reduce one | Limb 0 is one; all other limbs zero |

Each scenario loads the published field modulus, calls the actual production field operation, and compares the complete canonical limb array. These deterministic mathematical oracles isolate field arithmetic; they do not substitute for the existing RFC section 5.2 scalar multiplication vectors and section 6.2 Alice/Bob public-key and shared-secret vectors.

The existing full KATs live at `test/01_unit/lib/crypto/curve448_rfc7748_kat_spec.spl`: TV1, TV2, one iteration, Alice public key, Bob public key, and both directions of the shared secret. Their published expected bytes are unchanged. The wrapper `os.crypto.x448` also needs qualified integration execution; these field tests do not prove wrapper behavior.

No binary/protocol capture exists. Branch numerator, denominator, and percentage are **UNMEASURED**. After qualified execution, run spipe-docgen and replace this authored provenance with retained execution evidence; require zero stubs without weakening or replacing the oracles.
