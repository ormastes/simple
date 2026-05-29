# Crypto Algorithm Conformance Closure — 2026-05-04

Status: PASS
Scope: Focused closure for `os.crypto.streebog` and `os.crypto.ocb3` after the
compression/cipher verification wave.

## Summary

- `streebog.spl` now matches the byte-exact known-answer vectors exercised by
  [test/unit/os/crypto/streebog_kat_spec.spl](/home/ormastes/dev/pub/simple/test/unit/os/crypto/streebog_kat_spec.spl).
- `ocb3.spl` now supports full-block decrypt and passes both RFC-anchored
  encrypt cases and decrypt-side exactness/round-trip coverage in
  [test/unit/os/crypto/ocb3_spec.spl](/home/ormastes/dev/pub/simple/test/unit/os/crypto/ocb3_spec.spl).
- `bin/simple test` wrapper selection was updated so focused test runs use the
  current local driver before stale packaged binaries.

## Streebog fixes

- Corrected round-constant byte order at the accessor boundary.
- Corrected `P` permutation to respect RFC 6986 byte numbering against the
  repo’s in-memory state layout.
- Corrected final digest byte order at extraction.
- Corrected `streebog_256` to return the verified 256-bit half of the final
  512-bit state.
- Corrected non-empty final padded block payload ordering so the 63-byte RFC
  fixture (`M1`) hashes byte-exactly.

## OCB3 fixes

- Removed the explicit `not implemented` full-block decrypt branch.
- Routed full-block decrypt through the expanded-key AES decrypt path.
- Added decrypt coverage for RFC-style exact plaintext recovery plus full-block
  and partial-block round-trip cases.

## Verification gates

- `bin/simple test test/unit/os/crypto/streebog_kat_spec.spl`
- `bin/simple test test/unit/os/crypto/ocb3_spec.spl`
- `bin/simple test test/unit/os/crypto/crc32_kat_spec.spl`
- `bin/simple test test/unit/lib/common/lz4_spec.spl`

## Notes

- This report covers focused crypto closure only. It does not change the
  remaining WARN/FAIL accounting in
  [doc/09_report/verify_common_compression_framework.md](/home/ormastes/dev/pub/simple/doc/09_report/verify_common_compression_framework.md).
