# ECDSA P-256 SPKI header binding

Status: **AUTHORED_UNRUN / UNMEASURED**. Source-discovered defect; no observed
runtime RED/GREEN, no admitted native runtime and no branch coverage claim.

Owner: `src/lib/common/crypto/ecdsa_p256.spl`, `_spki_to_ec_point`.
Previously only total length 91 and point tag 04 at offset 26 were checked.
The wrapper discarded all 26 DER header bytes before calling a raw-point
verification backend. Altered algorithm/curve OIDs, ASN.1 lengths/tags and
BIT STRING unused-bit count therefore could not be validated by that backend.
Cryptographic acceptance of a malformed header is a source-based inference,
not a runtime observation in this session.

Contract/caller review: the common API explicitly documents a 91-byte SPKI
and uncompressed point; `std.common.crypto.typed.asym.ecdsa_p256_typed_verify`
documents DER P-256 SPKI and delegates to it. Existing common CAVP fixtures
use the canonical 26-byte prefix. No compressed-key support is removed by
this change: such keys already fail the fixed length/point-tag checks.
This patch is not a general ASN.1 parser or expansion of supported encodings.

REQ-TLS-ECDSA-SPKI-001 references official RFC 5480:
https://www.rfc-editor.org/rfc/rfc5480.txt, pinned TXT SHA-256
`593bf29fd0da2ff8b903c3ebf1c9d189a770039159e2ba46a0c3b91355037f26`.
§2.1.1 p. 4 specifies id-ecPublicKey and required parameters;
§2.1.1.1 p. 6 identifies secp256r1; §2.2 p. 7 specifies ECPoint octet-to-bit
mapping and uncompressed 04 encoding. Zero unused bits follows the complete
octet mapping with DER; RFC 5480 does not explicitly spell out this count byte.
The API's fixed 91-byte/uncompressed restriction is a repository contract,
not the full set of RFC 5480 encodings. No FIPS conformance is claimed.

Repair validates the exact canonical prefix before slicing the point. Existing
signature-length, SPKI-length and point-tag error precedence is retained.
Malformed headers return `E-SFFI-010: invalid ECDSA P-256 SPKI header`.

Regression: `test/01_unit/lib/common/crypto/ecdsa_spki_header_validation_spec.spl`.
Six scenarios reuse the existing NIST CAVP SigVer public key/message/signature:
canonical success, changed algorithm OID, changed curve OID, unused bit count,
outer length and outer tag. Each mutation preserves a valid point/signature;
the positive control prevents wholesale rejection from satisfying the suite.
The source fixture provenance is the existing common ECDSA KAT, not newly
downloaded FIPS test data. All calls target the common public verifier through
an alias; native symbol binding and foreign runtime execution remain pending.

Manual: `doc/06_spec/01_unit/lib/common/crypto/ecdsa_spki_header_validation_spec.md`.
The authored mirror embeds source and its hash, with no invented artifact hash.
Before claiming completion: execute six cases, existing common wrapper boundary
cases and KATs, required core/MCP native smoke, branch instrumentation, and
admitted zero-stub spipe-docgen. No bootstrap or seed fallback was run.
Root source-repair lane owns integration; Astra owns exact-commit source review.
