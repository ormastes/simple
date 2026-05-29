# Vec4i-Compatible SIMDification Targets — Survey
# Wave L / L4 — 2026-05-02

Scope: identify ciphers, hash functions, DSP primitives, and image-processing
kernels in `src/lib/` that fit the existing `Vec4i` (4 × i32, 128-bit SSE/NEON)
lane shape demonstrated by ChaCha20 (K5).  Survey period: 2026-05-02.

Companion docs:
- `doc/01_research/cipher_simd_patterns_2026-05-02.md` (J2) — cipher baseline
- `doc/01_research/loop_vectorize_targets_2026-05-02.md` (J4) — DSP/image loops

---

## §1  Existing Vec4i Primitive Inventory

Source: `src/lib/nogc_sync_mut/simd.spl:193` (struct) and `:350-387` (externs).

### §1.1  Vec4i struct

```
struct Vec4i:            # simd.spl:193
    x: i32
    y: i32
    z: i32
    w: i32
```

128-bit register; maps to `__m128i` (x86 SSE2) / `int32x4_t` (AArch64 NEON) /
`vint32m1_t` (RISC-V V).

### §1.2  Declared extern primitives (simd.spl:350-387)

| Wrapper fn | Extern | Op |
|---|---|---|
| `simd_add_i32x4` | `rt_simd_add_i32x4` | element-wise add |
| `simd_sub_i32x4` | `rt_simd_sub_i32x4` | element-wise subtract |
| `simd_mul_i32x4` | `rt_simd_mul_i32x4` | element-wise multiply |
| `simd_xor_i32x4` | `rt_simd_xor_i32x4` | bitwise XOR |
| `simd_and_i32x4` | `rt_simd_and_i32x4` | bitwise AND |
| `simd_or_i32x4`  | `rt_simd_or_i32x4`  | bitwise OR |
| `simd_shl_i32x4` | `rt_simd_shl_i32x4` | logical left-shift (uniform n) |
| `simd_shr_i32x4` | `rt_simd_shr_i32x4` | logical right-shift (zero-fill) |

Phase 1 note from chacha20.spl:16-17: `rt_simd_add_i32x4` is declared but was
"UNWIRED" in Phase 1.  ChaCha20 uses struct-field arithmetic (`_vadd`) as the
fallback.  If the extern is now wired (check runtime), `_vadd` can be replaced.

### §1.3  Aliases (simd/aliases.spl:47-49)

```
type Vec4i  = FixedVec<i32>    # aliases.spl:47
type Vec8i  = FixedVec<i32>    # aliases.spl:48
type Vec16i = FixedVec<i32>    # aliases.spl:49
```

Inert until D3/E2 (type-alias resolver not yet wired — parser_decls.spl:1086).
Construction today: `Vec4i(x: a, y: b, z: c, w: d)` struct literal or
`vec4i_splat(v)` wrapper (`aliases.spl:103`).

### §1.4  Adjacent types in scope (for comparison)

| Type | Declared at | Primitives wired? |
|---|---|---|
| `Vec8i` (i32x8) | simd.spl:220 + :395-430 | YES (8 ops) |
| `Vec16u8` (u8x16) | simd.spl:454 | add only (Phase 2 seed) |
| `Vec2u64` (u64x2) | simd.spl:566 | xor + PCLMUL (Phase 3) |
| `Vec4f` (f32x4) | simd_vector_types.spl:57 + simd.spl:260 | YES (5 ops) |
| `Vec4u` / `Vec4u32` | aliases.spl:52 | NONE — no u32x4 externs |
| `Vec4i64` | aliases.spl: not present | NONE — no i64x4 externs |

Gap: `Vec4u32` and `Vec4i64` have no backing externs.  See
`doc/08_tracking/feature_request/simd_u32x4_i64x4_intrinsics_2026-05-02.md`.

---

## §2  Salsa20/8 — Strongest Vec4i Target

### §2.1  Location

| File | Key function | Line |
|---|---|---|
| `src/lib/common/scrypt/salsa20.spl` | `salsa20_quarterround` | 11 |
| `src/lib/common/scrypt/salsa20.spl` | `salsa20_8_core` | 57 |
| `src/lib/common/scrypt/scrypt.spl` | calls `salsa20_8_core` in ROMix | ~1 |

### §2.2  Kernel Shape

The Salsa20/8 quarter-round (`salsa20.spl:11-45`) is:

```
b ^= (a + d) <<< 7
c ^= (b + a) <<< 9
d ^= (c + b) <<< 13
a ^= (d + c) <<< 18
```

`salsa20_8_core` (`salsa20.spl:57-101`) runs 4 double rounds.  Each double
round: 4 column quarter-rounds + 4 row quarter-rounds = 8 Vec4i-shaped ARX ops.

The state is 16 × u32 (64 bytes).  Vertical 4-block layout (same as ChaCha20
`_chacha20_block4_simd`, `chacha20.spl:179`): pack the same word index from 4
independent Salsa20 calls into one Vec4i lane.  No inter-lane shuffles are
needed for the vertical layout.

### §2.3  Required Vec4i Ops vs. Available

| Op | Salsa20 use | Available? |
|---|---|---|
| `_vadd` (struct-field add) | a+d, b+a, c+b, d+c | YES (struct literal) |
| `simd_xor_i32x4` | XOR with rotated result | YES (simd.spl:371) |
| `simd_shl_i32x4` + `simd_shr_i32x4` + `simd_or_i32x4` | rotl 7/9/13/18 | YES (simd.spl:383-387, 379) |

Rotation amounts (7, 9, 13, 18) are all constant — identical pattern to
ChaCha20's `_vrotl16`, `_vrotl12`, `_vrotl8`, `_vrotl7` helpers
(`chacha20.spl:40-54`).  A shared `simd_rotl_i32x4(v, n)` wrapper (pure `.spl`,
see §M.1) would serve both.

### §2.4  Expected Speedup

scrypt memory-hard hashing (`scrypt.spl`) calls `salsa20_8_core` in the ROMix
inner loop: 2*N calls per block (N = cost parameter).  For N=32768, ~65,536
Salsa20/8 cores per scrypt invocation.  A 4× throughput improvement via
vertical 4-block SIMD matches the NaCl/libsodium benchmark: ~3.5 GB/s vs
~0.9 GB/s scalar on a 3 GHz x86_64 (SnappyCrypto bench, 2013, cited by
D. J. Bernstein https://cr.yp.to/snuffle/speed.html).

### §2.5  Difficulty

**EASY** — all required ops exist.  Implementation mirrors `chacha20.spl:179`
exactly.  Estimate: ~60 additional lines in `salsa20.spl`.

---

## §3  SHA-1 Multi-Block — Vertical 4-Block Path

### §3.1  Location

| File | Key function | Line |
|---|---|---|
| `src/lib/common/crypto/sha1.spl` | `sha1_process_block` | 105 |
| `src/lib/common/crypto/sha1.spl` | `sha1_f` (round function selector) | 34 |
| `src/lib/common/crypto/sha1.spl` | `sha1_k` (round constant) | 51 |

### §3.2  Kernel Shape

`sha1_process_block` (`sha1.spl:105-170`):
- 80-word message schedule (linear recurrence — not vectorizable within one block)
- 80 serial rounds: each round reads `a..e`, computes `f(b,c,d)`, rotates `a`
  by 5, rotates `b` by 30, advances.

**Within a single block, the 80 rounds are fully serial** (each round reads the
output of the previous).  SHA-1 CANNOT be intra-block SIMDified with Vec4i.

**Vertical 4-block parallelism IS applicable**: pack the same round state
variable from 4 independent messages into one Vec4i lane.  Each lane processes
an independent SHA-1 computation; all 80 rounds proceed in lockstep.

Required ops per round (vertical):
- `_vadd` (mod-2^32 add for a+f+e+K+W)
- `simd_xor_i32x4` (f-function for rounds 20-39 and 60-79)
- `simd_and_i32x4` / `simd_or_i32x4` / `simd_shr_i32x4` (f-function Ch/Parity/Maj)
- `simd_shl_i32x4` + `simd_or_i32x4` for rotl5 and rotl30

All ops available.

### §3.3  Required Vec4i Ops vs. Available

| Op | SHA-1 use | Available? |
|---|---|---|
| add (struct literal) | `temp = rotl5(a)+f+e+K+W` | YES |
| `simd_xor_i32x4` | Parity f-function rounds 20-39, 60-79 | YES |
| `simd_and_i32x4` | Ch/Maj f-functions | YES |
| `simd_or_i32x4`  | Ch/Maj f-functions | YES |
| `simd_shl_i32x4` + `simd_shr_i32x4` | rotl5(a), rotl30(b) | YES |

### §3.4  Expected Speedup

4× throughput for batch-SHA-1 workloads (4 independent messages).  Relevant
use-case: HMAC-SHA1 for multiple TLS PSK tickets, Git SHA-1 batch verification.
Intel measured ~4× improvement for 4-way SHA-1 SIMD
(Intel document 323641, "Improving the Performance of the Secure Hash Algorithm
(SHA) Using Intel® Streaming SIMD Extensions (Intel® SSE4)", 2012).

### §3.5  Difficulty

**MEDIUM** — all ops exist.  The complication: SHA-1's `f` function selects
between three formulas based on round index.  A pure-Simple implementation must
branch on round group (0-19, 20-39, 40-59, 60-79) or precompute.  SIMD ops
are available; refactoring `sha1_process_block` to accept 4 independent
inputs and operate vertically is ~100 lines.

---

## §4  CRC32 — Table-Lookup Is Not Vec4i; PCLMUL Path Is Vec2u64

### §4.1  Location

| File | Key function | Line |
|---|---|---|
| `src/lib/nogc_sync_mut/compression/gzip/crc.spl` | `crc32_calculate` | 26 |
| `src/lib/nogc_sync_mut/compression/gzip/crc.spl` | `crc32_update` | 47 |
| `src/lib/nogc_sync_mut/simd.spl` | `rt_simd_clmul_lo_u64` / `rt_simd_clmul_hi_u64` | ~580 |

### §4.2  Kernel Shape

The current implementation (`crc.spl:26-44`) is a 4-bit table-lookup loop:

```
for each byte:
    index = (crc ^ byte) & 0x0f
    crc = (crc >> 4) ^ table[index]
```

This is **serial** (each iteration depends on `crc` from the previous) and
uses only 16 table entries.  Not Vec4i-compatible.

**PCLMUL / carryless-multiply path** (Intel patent PCT/US2009/039555):
CRC32 over a byte stream can be computed via `CLMUL` (GF(2) polynomial multiply)
by folding 128-bit chunks using reduction polynomials.  This uses `Vec2u64`
(`simd.spl:566`), NOT `Vec4i`.  The `rt_simd_clmul_lo_u64` /
`rt_simd_xor_u64x2` externs are already declared in `simd.spl:~580`.

**Vec4i applicability: NONE** — CRC32 is u8/u32 serial by polynomial structure.

**Vec2u64 PCLMUL path: FEASIBLE TODAY** (existing primitives) but is a separate
workstream from the Vec4i wave.

### §4.3  Difficulty

Table-lookup path: NOT vectorizable — skip.
PCLMUL path via Vec2u64: **HARD** — requires implementing the folding algorithm
from scratch (~150 lines), GF(2) reduction constants, and handling tail bytes.
References: Intel Application Note 323102 "Fast CRC Computation for Generic
Polynomials Using PCLMULQDQ Instruction" (2009).

---

## §5  Image Transforms — DCT / RGB→YUV — Vec4i Not the Right Shape

### §5.1  Location

| File | Contents |
|---|---|
| `src/lib/common/image/png_decode.spl` | PNG to ARGB pixel conversion |
| `src/lib/common/image/deflate_inflate.spl` | Deflate decompression |

No DCT or RGB→YUV transform exists in `src/lib/common/image/`.  The directory
contains only `png_decode.spl`, `deflate_inflate.spl`, `ppm_decode.spl`, and
`__init__.spl`.

### §5.2  PNG Pixel Pack Loop

`png_decode.spl:131-141` packs RGBA bytes into `u32` ARGB words:

```
val pixel = (a << 24) | (r << 16) | (g << 8) | b
```

This is a `Vec16u8` / `Vec4u32` pattern (4 channels per pixel), NOT Vec4i.
It could be SIMDified with `Vec16u8` byte-shuffle but requires `simd_shuffle_u8x16`
(not yet exposed — see `simd.spl` Phase 2 comment: "simd_shuffle_u8x16 deferred
to follow-up waves").

### §5.3  Shape Assessment

- DCT (8×8 → 4×4): not present in stdlib.
- RGB→YUV matrix-vector: not present in stdlib.
- PNG filter Up/Sub/Paeth: serial inter-pixel dependency for Paeth; Up and Sub
  could use `Vec16u8` (J4 §R4 notes this as a top-5 target) — but NOT Vec4i.

**Vec4i applicability: NONE for existing image code**.

---

## §6  FFT Butterfly — f64 Not i32; Not Vec4i

### §6.1  Location

| File | Key function | Line |
|---|---|---|
| `src/lib/common/fft/fft.spl` | `fft_radix2` | 8 |
| `src/lib/common/fft/fft.spl` | `bluestein_fft` | 83 |
| `src/lib/common/signal_processing/transform.spl` | signal gen / windowing | ~1 |

### §6.2  Shape Assessment

`fft_radix2` (`fft.spl:8`) operates on `[(f64, f64)]` complex tuples.  Each
butterfly requires:

- 2 × f64 multiply
- 2 × f64 add/subtract

These map to `Vec4d` (f64x4) or `Vec4f` (f32x4) — not `Vec4i`.  `Vec4d`
externs exist (`simd.spl:320-342`).

**Vec4i applicability: NONE** — FFT uses floating-point arithmetic throughout.
A fixed-point i32 FFT would map to Vec4i but none exists in `src/lib/`.

---

## §7  Hash Functions — BLAKE2/BLAKE3 and xxHash32 Not Present

### §7.1  Location

```
find src/lib -name 'blake*'   → (no output)
find src/lib -name '*xxhash*' → (no output)
```

Neither BLAKE2s, BLAKE2b, BLAKE3, nor xxHash32 exists as a `.spl` file in the
stdlib.  `hash_utils.spl` contains `fnv_hash`, `djb2`, and simple string
hashers — no 32-bit ARX hash chains.

### §7.2  Shape Assessment (Would-Benefit-If-Added)

**BLAKE2s** (32-bit) / **BLAKE3** (32-bit subtree compression):
- G-function is `a += b + m; d = rotl(d^a, 16); c += d; b = rotl(b^c, 12); ...`
- Identical ARX pattern to ChaCha20 quarter-round
- 4 independent G-function calls per round → Vec4i vertical layout
- Required ops: `_vadd`, `simd_xor_i32x4`, `simd_shl_i32x4`, `simd_shr_i32x4`,
  `simd_or_i32x4` — ALL available
- Expected speedup: ~3-4× (BLAKE3 official benchmark: ~1.0 cpb SIMD vs ~3.5 cpb
  scalar on x86_64)

**xxHash32**:
- 4-lane accumulator `acc[0..3]` each processes one lane of input independently
- Perfect Vec4i fit: `acc[i] = rotl32(acc[i] + val*PRIME2, 13) * PRIME1`
- Requires `simd_mul_i32x4` (available) + rotl helpers
- Expected speedup: 2-4× (xxHash official bench, https://github.com/Cyan4973/xxHash)

**Vec4i applicability: HIGH for both** — but neither file exists to modify.

---

## §8  Geometry / Linear Algebra — f64 Structs, Not i32

### §8.1  Location

| File | Key type | Lane type |
|---|---|---|
| `src/lib/common/engine/math3d.spl:211` | `Vec4` struct | `f64` |
| `src/lib/common/linear_algebra/matrix_ops.spl:416` | `la_matrix_multiply` | `[[f64]]` |
| `src/lib/common/geometry/*.spl` | `point`, `circle`, `polygon` | `f64` |

### §8.2  Shape Assessment

`math3d.spl:211-233` defines a `Vec4` class with `x,y,z,w: f64`.  All arithmetic
is scalar `f64`.  Matrix operations in `matrix_ops.spl` use `[[f64]]` (array of
arrays of f64).

**Vec4i applicability: NONE** — all geometry/linalg code uses f64.  The correct
SIMD target is `Vec4d` (`simd.spl:320-342`, 5 ops already available).

---

## §M  Pattern Catalog — Vec4i Ops Needed But Not Exposed

### §M.1  `simd_rotl_i32x4` — Pure-`.spl` Wrapper (No Rust Seed Required)

**Pattern**: rotate-left by constant `n` = `shl(v, n) | shr(v, 32-n)`

Used by ChaCha20 at `chacha20.spl:40-54` (four separate `_vrotl16`, `_vrotl12`,
`_vrotl8`, `_vrotl7` helpers).  The same pattern would be needed verbatim for
Salsa20 (rotl 7/9/13/18) and BLAKE2s/3 (rotl 16/12/8/7).

Proposed wrapper:
```
fn simd_rotl_i32x4(v: Vec4i, n: i64) -> Vec4i:
    """Rotate-left each i32 lane by n bits (n in 1..31)."""
    simd_or_i32x4(simd_shl_i32x4(v, n), simd_shr_i32x4(v, 32 - n))
```

**This is a pure-`.spl` follow-up wave item** — add to `simd.spl` after the
existing `simd_shr_i32x4` at line 387.  No Rust-seed work required.

### §M.2  Lane Shuffle / Permute — Requires Rust Seed

**Pattern**: move lanes between positions, e.g., `[a,b,c,d] → [b,c,d,a]`

Needed for:
- SHA-256 message schedule W[i] depends on W[i-2], W[i-7], W[i-15], W[i-16]
  — a 4-lane horizontal shuffle would pack 4 schedule words at once
- SHA-1 diagonal-round permutation (if ever restructured)
- BLAKE2 diagonal rounds (same as ChaCha20 diagonal — NOT needed for vertical
  4-block layout, only for horizontal single-block layout)

No `simd_shuffle_i32x4` or `simd_blend_i32x4` exists.  This requires a Rust-seed
extern:

```
rt_simd_shuffle_i32x4(a: Vec4i, b: Vec4i, mask: i64) -> Vec4i
```

Maps to `_mm_shuffle_epi32` (x86) / `vextq_s32` / `vtbl1_s32` (NEON).
**File as a follow-up FR** — not a pure-`.spl` item.

### §M.3  Vec4u32 and Vec4i64 Externs — Rust Seed Required

See `doc/08_tracking/feature_request/simd_u32x4_i64x4_intrinsics_2026-05-02.md`.

Absence forces the `_u32_to_i32` cast workaround in `chacha20.spl:64-75`.
The `Vec4u = FixedVec<u32>` alias (`aliases.spl:52`) is already declared but
has no backing primitives — it is inert for both the D3/E2 type-alias reason
AND the missing-externs reason.

### §M.4  `simd_add_i32x4` Wiring Verification

`chacha20.spl:16-17` notes that `rt_simd_add_i32x4` was "UNWIRED in Phase 1".
If it is now wired in the runtime, the `_vadd` struct-field fallback in
`chacha20.spl:36-38` can be replaced with a direct `simd_add_i32x4` call.
This is a cleanup item, not a new feature.

---

## §M+1  Recommendations — Top-5 Vec4i-Wave Targets

### R1  Salsa20/8 SIMD Rewrite — EASY, High Impact

**File**: `src/lib/common/scrypt/salsa20.spl:57`
**Why**: Identical ARX structure to ChaCha20.  All Vec4i ops available.
Vertical 4-block layout requires no shuffles.  scrypt memory-hard hashing is
the direct consumer; a 4× throughput gain materially reduces password-hashing
latency.  Estimated effort: ~60 lines.

### R2  SHA-1 Vertical 4-Block Path — MEDIUM, Targeted Impact

**File**: `src/lib/common/crypto/sha1.spl:105`
**Why**: SHA-1 is still used in Git object hashes and legacy TLS/HMAC.  Batch
verification of 4 independent messages benefits directly.  The 80-round serial
loop becomes embarrassingly parallel at the message level.  All Vec4i ops
available.  Estimated effort: ~100 lines.

### R3  `simd_rotl_i32x4` Pure-`.spl` Wrapper — TRIVIAL

**File**: `src/lib/nogc_sync_mut/simd.spl` (after line 387)
**Why**: A single 3-line wrapper shared by ChaCha20, Salsa20, BLAKE2s/3, and
any future ARX cipher.  Zero Rust-seed work.  Eliminates copy-pasted `_vrotl*`
helpers.

### R4  Vec4u32 / Vec4i64 Extern Wave — MEDIUM (Rust seed)

**File**: `src/compiler_rust/` + `simd.spl` + `aliases.spl`
**Why**: Eliminates the `_u32_to_i32` cast wrapper in ChaCha20; unblocks
SHA-512 SIMD (no current workaround).  See
`doc/08_tracking/feature_request/simd_u32x4_i64x4_intrinsics_2026-05-02.md`.

### R5  CRC32 via PCLMUL / Vec2u64 — HARD but High Impact

**File**: `src/lib/nogc_sync_mut/compression/gzip/crc.spl`
**Why**: CRC32 appears in every gzip/zlib/PNG decode and TLS record.  The
PCLMUL externs (`rt_simd_clmul_lo_u64`, `rt_simd_xor_u64x2`) are already
declared in `simd.spl:~580`.  This is Vec2u64-shaped, not Vec4i, but it is
the most impactful standalone SIMD addition adjacent to this wave.

---

## Appendix A — Targets Evaluated and Excluded

| Target | Why Excluded |
|---|---|
| FFT butterfly (`fft/fft.spl:8`) | f64 throughout; maps to Vec4d, not Vec4i |
| Geometry / math3d (`math3d.spl:211`) | f64 Vec4; use Vec4d path |
| Linear algebra (`matrix_ops.spl:416`) | `[[f64]]` layout; Vec4d or f64x8 |
| PNG pixel pack (`png_decode.spl:131`) | Vec16u8 byte-shuffle path; not Vec4i |
| PNG filter Paeth | Serial inter-pixel dependency; not vectorizable |
| BLAKE2/BLAKE3 | Not present in stdlib; would benefit if added |
| xxHash32 | Not present in stdlib; would benefit if added |
| MD5 | Not present in stdlib; serial round dependency within block |
| CRC32 table-lookup | Serial by polynomial structure; not Vec4i |

## Appendix B — Files Confirmed Absent

```
find src/lib -name 'blake*'     → (no output)
find src/lib -name '*xxhash*'   → (no output)
find src/lib -name 'md5*'       → (no output)
find src/lib -name 'salsa20*'   → src/lib/common/scrypt/salsa20.spl (found)
find src/lib -name 'sha1*'      → src/lib/common/crypto/sha1.spl (found)
find src/lib -name 'crc*'       → src/lib/nogc_sync_mut/compression/gzip/crc.spl
```
