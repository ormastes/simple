# Pinned Phase 2 CRC32 i64 boundary retains unexpected high bits

Canonical ID: `phase2_crc32_i64_width_spill_2026_10_27`. Status: fix-implemented-verification-pending. Owner: compiler/runtime CRC boundary. Created: 2026-10-27.

A native append-only registry copy preserved all original payload bytes but wrote CRC header -2292158518 while independent unsigned zlib computed2002808778. The values differ by2^32. This proves a CRC width or ABI boundary discrepancy; the exact widening or complement cause is not isolated. Masking public i64 CRC outputs to their low32bits preserves the actual CRC register contract.

## Evidence

Cycle3 canonical API compile0 and copy-run0 were not passing evidence because the independent strict CRC oracle failed. Exact old-body preservation passed after removing only28newrowlines, including all5265oldrows and20opaqueoverwide rows. Real canonical registry remained untouched. New actual KAT and copy qualification are required before registration.

## Removal condition

Retire the explicit width normalization only after the deployed producer passes text123456789 CRC3421780262, empty input, chunked update through high-bit-set states and independent unsigned zlib comparisons for real registry bodies. Never accept negative header CRC or relax the external oracle.

No compiler rebuild or exact root-cause claim is made. Public CRC values remain unsigned32-bit values carried in i64.

**Revalidated 2026-11-02: still plausible because Canonical ID: phase2_crc32_i64_width_spill_2026_10_27. Status: fix-implemented-verification-pending. Owner: compiler/runtime CRC boundary. Created: 2026-10-27; no merged fix commit with a passing regression is cited in this doc.**

## Root cause and fix (2026-11-03, lane s3g2)

Static root cause: the Cranelift lane keeps every int SSA value as I64 and treats widening casts as no-ops (`cl_translate_cast`, "already canonically-extended"), but `cl_translate_binop`/`cl_translate_unaryop` never re-canonicalised U8/U16/U32 results of Add/Sub/Mul/Shl/Neg/BitNot, so `~x`, wrapped `a - b`, `a << 8` leave bits above bit 31 and a later `.to_i64()` exposes them (-2292158518 = 2002808778 - 2^32). Fix: `cl_canonicalize_unsigned_narrow` (ireduce + uextend) applied to BinOp/UnaryOp results typed U8/U16/U32 in `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`. Workaround tags in crc.spl are kept.

Spec: `test/01_unit/lib/nogc_sync_mut/compression/crc32_u32_width_spill_spec.spl` (passes in interpreter; the defect is native-only).

Stage3 verify: build a native producer containing this commit, `native-build` the spec/KAT program, run; expect crc 3421780262 and 4294967295/3989547399 checks pass; then retire the workaround per the removal condition.
