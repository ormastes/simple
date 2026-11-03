# SQLCipher4 session and IV-source boundaries

Status: **AUTHORED_UNRUN**. This is an authored manual, not generated docgen output.
Proof class: production codec function-record integration with synthetic session material.
No admitted self-hosted runtime was supplied. Simple execution, docgen zero-stub
validation, sabotage execution and branch measurement remain unrun.
Coverage numerator/denominator: **UNMEASURED**, not 99%.

Spec: `test/02_integration/app/devhub/messenger/sqlcipher_session_boundaries_spec.spl`
Spec SHA-256: `21b48c2a9bc598452f12520db59aa784d120e515264fdac94ad1a25fd9a42fc5`
Oracle artifact: `test/fixtures/database/sqlcipher4/boundary_oracles.sdn`
Artifact SHA-256: `f6401ed8b0a7601a9f3c05074767616278bd382f315088793e7c47e30a0c3f4a`
Independent generator: `test/fixtures/database/sqlcipher4/gen_boundary_oracles.py`
Generator SHA-256: `6a763858f420b5ae6cf13f7f73c508a06e25ea9655fc408f10af4874281681b5`

## Manual flow

1. Construct public synthetic opaque session buffers of lengths 0, 79 and 81.
2. Call the actual codec record encode/decode functions; require `CORRUPT_PAGE`.
3. Supply a closed 80-byte session; require `MISSING_SECRET` in both directions.
4. Supply an open 80-byte session and empty pages; require the subsequent
   `INVALID_PAGE_GEOMETRY` error as a positive control for session admission.
5. Supply a complete virtual body and RNGs returning 0, 15 and 17 bytes;
   require `CORRUPT_PAGE`, not an encoded result.

REQ-CIPHER-BOUNDARY-003 covers the session-open and material-length gates.
REQ-CIPHER-BOUNDARY-004 covers exact IV width at the function-record boundary.
These are repository API contracts, not claims imposed by the SQLCipher wire
format. Synthetic material does not prove passphrase opening or Messenger
end-to-end behavior. The already existing record roundtrip and dense Messenger
specs own successful encryption and encrypted database reads.

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
