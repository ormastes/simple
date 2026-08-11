# NEON and RVV ML-KEM NTT candidates are declared but have no vector kernel

**Status:** OPEN — fail-closed; do not promote ARM or RISC-V SIMD.

**Scope:** `X25519MLKEM768` candidate execution on AArch64 NEON and RISC-V V.

`src/lib/nogc_sync_mut/simd.spl:767` implements only the AVX2 i32x8 NTT
butterfly path.  It returns an empty batch unless `has_avx2()` is true, and
`mlkem_ntt_simd_backend()` therefore returns only `1` (AVX2) or `0` (no
executed SIMD kernel).  `execution_policy.spl` correctly requires code `2`
for NEON and `3` for RVV, so both requested candidates reject rather than
misrepresent scalar work as SIMD evidence.

The native profile now reports NEON/RVV capability accurately, but capability
is not execution proof.  The required completion work is:

1. Implement byte-identical NEON and RVV butterfly kernels over the pinned
   256-coefficient ML-KEM polynomial input.
2. Emit only actual chunk counts; RVV must record observed VLEN (at least 128,
   divisible by 32).
3. Add native same-fixture scalar-vs-NEON/RVV Set A/B/C tests and retained
   timing receipts with at least 30 measured samples.
4. Run each lane on physical AArch64 and RISC-V hosts before promotion.

No configuration-only or synthetic measurement can close this issue.

## Re-verification (2026-08-10)

Confirmed unchanged: `mlkem_ntt_simd_batch` in `src/lib/nogc_sync_mut/simd.spl`
still gates on `has_avx2()` only (lines 791, 829); no NEON or RVV butterfly
path exists. This Linux dev host is `x86_64` (`uname -m`), so it has neither
AArch64 NEON nor RISC-V V hardware to implement or test against — the
completion checklist (byte-identical NEON/RVV kernels, VLEN-aware chunk
counts, same-fixture scalar-vs-vector tests, physical-host runs before
promotion) is unchanged and remains genuinely out of scope for this
environment. No fix attempted; status remains OPEN/fail-closed as filed.
