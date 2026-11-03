# SQLCipher4 page-number bounds

Status: AUTHORED_UNRUN. Authored manual, not docgen output.
The integer guards are present in production; these cases discriminate untested upper and negative bounds.
Proof class: production raw page geometry contract.
Coverage: UNMEASURED. No 99% claim, no runtime admission, no generated zero-stub claim.

Spec: `test/01_unit/lib/database/codec/sqlcipher4_page_bounds_spec.spl`

Spec SHA-256: `f3a5cdc3212090f642c282fb4764d1143a30fead084e648138f97473b1855886`

## Flow

1. Pass page numbers -1, 4294967296 and 9223372036854775807 with valid key,
   IV and page lengths through both production encode and decode entrypoints.
2. Require the exact `SQLCIPHER4_CORRUPT_PAGE` code before LE32 serialization.
3. Pass 4294967295 with a full zero page and require authentication failure,
   proving the upper representable bound reaches the next gate.

REQ-CIPHER-PAGE-BOUNDS-001 is the raw codec's explicit one-based LE32 domain,
not a promise that SQLite databases may contain 4294967295 pages. Existing
page spec tests only zero despite its broader scenario title. The earlier
boundary-oracles spec pins high-bit HMAC framing; this spec owns input admission.
No runtime-produced artifact exists; all byte arrays are explicit source inputs.

## Reference and admission limits

Pinned SQLCipher v4.6.1 source commit c5bd336ece77922433aaf6d6fe8cf203b0c299d5,
`src/sqlcipher.c`, SHA-256 010d418c541cd3606f58fd705ae404201fd243fd20cb387439697289a6c87219:
`sqlcipher_page_hmac` and `sqlcipher_page_cipher` bind IV/page number and verify
authentication before the cipher provider. SQLCipher profile source and official
API snapshot pin 4096-byte pages and 80-byte reserve for SHA512. NIST SP800-38A
section6.2 defines CBC. See the campaign supplemental_sources.md for full pins.

After a qualified runtime exists, run the spec and retain failure/success logs,
then generate the manual using spipe-docgen with zero stubs. Runtime checks,
source matched branch counts and docgen remain unexecuted.
