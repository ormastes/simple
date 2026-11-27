# SQLCipher4 binary derivation and page-number boundaries

Status: **AUTHORED_UNRUN**. This is an authored manual, not generated docgen output.
Proof class: production primitive calls with independent Python/OpenSSL oracle.
No admitted self-hosted runtime was supplied. Simple execution, docgen zero-stub
validation, sabotage execution and branch measurement remain unrun.
Coverage numerator/denominator: **UNMEASURED**, not 99%.

Spec: `test/01_unit/lib/database/codec/sqlcipher4_boundary_oracles_spec.spl`
Spec SHA-256: `012a78eac1666f183151f7206523937d400906faebd63820db34bf888572b3f8`
Oracle artifact: `test/fixtures/database/sqlcipher4/boundary_oracles.sdn`
Artifact SHA-256: `f6401ed8b0a7601a9f3c05074767616278bd382f315088793e7c47e30a0c3f4a`
Independent generator: `test/fixtures/database/sqlcipher4/gen_boundary_oracles.py`
Generator SHA-256: `6a763858f420b5ae6cf13f7f73c508a06e25ea9655fc408f10af4874281681b5`

## Manual flow

1. Load public binary password `00 7f 80 ff 00 41` and salt `00..0f`.
2. Open the production key session at the locked 256000-iteration SHA512 profile.
3. Compare all bytes of both derived 32-byte keys through `compare_evidence`
   with literal `check_exact` oracles, then close the session.
4. Authenticate ciphertext bytes `00 7f 80 ff`, IV `00..0f`, key `00..1f`
   with page numbers 255, 256, 65536, 2147483648 and 4294967295.
5. Require exact 64-byte fixed HMAC values for every page-number case.

REQ-CIPHER-BOUNDARY-001 preserves embedded NUL/high-bit passphrase bytes and
pins both PBKDF2 stages. RFC 8018 section 5.2 defines the derivation; SQLCipher
sets SHA512, 256000 iterations, 32 output bytes, and the masked-salt fast KDF.
REQ-CIPHER-BOUNDARY-002 pins SQLCipher little-endian 32-bit page-number framing.
The four-byte ciphertext is a framing-unit input, not a valid encrypted page.
The oracle generator uses Python hashlib/hmac backed by the provider recorded
in the artifact, independently of Simple. These are computed independent test
vectors, not claimed published SQLCipher known-answer vectors.

## Existing coverage and limits

The existing `sqlcipher4_keys_spec.spl` covers empty secrets, short/long salts,
raw-key rejection and profile mismatch. `sqlcipher4_page_spec.spl` covers
AES-256-CBC NIST SP 800-38A F.2.5, page geometry, wrong keys and plaintext
headers. `dense_codec_page_auth_spec.spl` already covers first/middle/last
ciphertext, IV and tag flips; swapped pages; cross-database pages; 0/4095/4097
byte lengths; and independent database fixture positive controls. Those cases
are referenced, not duplicated, and their historical execution is not newly
claimed. Authentication-before-decrypt timing/control-flow instrumentation
and a measured complete branch denominator remain outstanding.

After admission, execute this spec with the existing native test runner and
retain its artifacts, then run `spipe-docgen <spec> --output doc/06_spec --no-index`.
Do not promote this authored manual to generated PASS without that evidence.
