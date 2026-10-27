# Pinned Phase 2 CRC32 i64 boundary retains unexpected high bits

Canonical ID: `phase2_crc32_i64_width_spill_2026_10_27`. Status: open. Owner: compiler/runtime CRC boundary. Created: 2026-10-27.

A native append-only registry copy preserved all original payload bytes but wrote CRC header -2292158518 while independent unsigned zlib computed2002808778. The values differ by2^32. This proves a CRC width or ABI boundary discrepancy; the exact widening or complement cause is not isolated. Masking public i64 CRC outputs to their low32bits preserves the actual CRC register contract.

## Evidence

Cycle3 canonical API compile0 and copy-run0 were not passing evidence because the independent strict CRC oracle failed. Exact old-body preservation passed after removing only28newrowlines, including all5265oldrows and20opaqueoverwide rows. Real canonical registry remained untouched. New actual KAT and copy qualification are required before registration.

## Removal condition

Retire the explicit width normalization only after the deployed producer passes text123456789 CRC3421780262, empty input, chunked update through high-bit-set states and independent unsigned zlib comparisons for real registry bodies. Never accept negative header CRC or relax the external oracle.

No compiler rebuild or exact root-cause claim is made. Public CRC values remain unsigned32-bit values carried in i64.
