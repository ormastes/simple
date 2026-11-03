# NEON and RVV ML-KEM NTT candidates are declared but have no vector kernel
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Triage 2026-09-13 (BUGFIX-7 lane)

Out of lane: missing NEON/RVV vector-kernel feature work, not a bounded bug fix. No change made.


## Source repair candidate (2026-11-03; qualification pending)

Current release source already contains genuine AVX2, NEON and RVV NTT/INTT
kernels in `src/runtime/runtime_simd_dispatch.c`. The remaining first faulty
boundary was `std.simd`: it still selected only AVX2 and independently executed
old Vec8i butterflies instead of calling these native kernels. The candidate
routes the public facade to the existing `rt_mlkem_ntt_simd_*` provider and its
thread-local chunk/VLEN receipt. Unsupported hosts still return an empty batch;
the provider's scalar reference is never admitted as SIMD through this facade.

Contract: FIPS 203 Algorithms 9/10, 256 coefficients per polynomial, q=3329,
canonical residues on entry/output, independent polynomial batches. NEON uses
four i32 lanes, scalar stride-2 tails, and 192 butterfly chunks per polynomial.
AVX2 uses eight lanes and 80 chunks. RVV uses actual e32m1 VL for each strip,
records completed strips and observes VLEN through vsetvlmax; lane count is not
assumed to equal four. Inverse scale is 3303, and does not count as a butterfly
chunk. Reset, execution and receipt read must remain on one native thread.

Authored native regression:
`test/01_unit/os/crypto/mlkem_native_provider_boundary_spec.spl` compares the
same three-polynomial fixture against the existing scalar FIPS implementation,
checks inverse recovery, +/-2q representatives, alternating 0/q-1 values,
impulses at SIMD/group/polynomial edges and invalid 0/1/255/257 lengths.
This is scalar equivalence coverage, not an independently executed NIST KAT.
Existing C baseline and pinned fixture remain available through
`scripts/check/build-mlkem-simd-c-lane.shs`.

Verification: scoped diff whitespace check passed. All authored Simple behavior
checks are TEST_BLOCKED: no admitted self-hosted CLI is available on this host.
No seed execution was substituted. Physical AArch64 and RVV execution, exact
NIST vector qualification, retained Set A/B/C comparisons and at least 30 timing
samples per hardware lane remain UNRUN. Status remains OPEN pending those gates;
this source repair does not authorize SIMD promotion or a hardware PASS.

An additional authored independent FIPS 203 factor-root oracle transforms X^2
into pairs (17^(2*BitRev7(i)+1) mod 3329, 0), with inverse recovery. It is
also unexecuted and is not represented as NIST KAT execution evidence.
