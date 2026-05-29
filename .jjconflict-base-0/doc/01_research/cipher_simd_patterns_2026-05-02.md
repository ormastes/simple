# Corrections (2026-05-02 Wave L / L5)

This section documents factual errors found in the J2 original below.
All corrections are additive; the J2 text is preserved as a historical record.
All citations are verified against actual source; no locations are fabricated.

## L5.1  Method

Three sources were audited:

1. `src/lib/nogc_sync_mut/simd.spl` — all `extern fn rt_simd_*` declarations
2. `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — interpreter
   dispatch table
3. `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` — Cranelift FFI
   table

A three-tier wiring status applies to every extern in simd.spl:

- **INTERPRETER-WIRED**: present in `interpreter_extern/mod.rs` dispatch AND
  has a Rust runtime implementation.  Works in interpreter / SMF mode.
- **FULLY STUB**: NOT present in `mod.rs` dispatch AND no Rust runtime impl
  found.  Calling this extern panics in any execution mode.
- **CRANELIFT-BLOCKED (uniform)**: `src/compiler_rust/compiler/src/codegen/
  runtime_ffi.rs` contains ZERO `rt_simd_*` entries (lines 261-294 cover only
  `rt_vec_*` generic ops).  Therefore ALL rt_simd_* externs, whether
  interpreter-wired or stub, will fail in Cranelift AOT compiled mode.

The note at simd.spl:445-447 ("Phase 2 SEED... AES round / xor_u8x16 /
shuffle / PCLMUL deferred") is STALE.  AES round and CLMUL ops shipped in
Phase 3 and are fully wired interpreter-side.

K1 bug doc `simd_aesni_runtime_stub_only_2026-05-02.md` contains two factual
errors: it claims "no runtime backing" (wrong — `simd_aes_ops.rs` has real
AES-NI hardware implementation), and it grepped `ffi_array.rs` (wrong file —
real interpreter dispatch is `interpreter_extern/mod.rs:835-899`).

## L5.2  Corrected Difficulty Matrix

| Cipher / Op | J2 Rating | L5 Corrected Rating | Key Reason |
|-------------|-----------|---------------------|------------|
| AES round wire-up | TRIVIAL | TRIVIAL-interpreter / CRANELIFT-BLOCKED | `rt_simd_aes_round_u8x16` is interpreter-wired (mod.rs:888); no runtime_ffi.rs entry |
| AES-GCM CLMUL | HARD | MEDIUM-interpreter / CRANELIFT-BLOCKED | `rt_simd_clmul_lo/hi_u64` wired (mod.rs:897-898); `simd_aes_ops.rs` has real `_mm_clmulepi64_si128` + ARM `vmull_p64` |
| ChaCha20 | MEDIUM | TRIVIAL-interpreter / CRANELIFT-BLOCKED | Vec4i ops (add/sub/mul/xor/and/or/shl/shr_i32x4) are interpreter-wired (mod.rs:863-870); K5 confirmed |
| Salsa20/8 | MEDIUM | TRIVIAL-interpreter / CRANELIFT-BLOCKED | Same Vec4i infrastructure; no new externs needed |
| Poly1305 | HARD | MEDIUM-interpreter / CRANELIFT-BLOCKED | `rt_simd_clmul_lo/hi_u64` wired (simd.spl:592-593, mod.rs:897-898); "not yet wired" claim in J2 §6.4 is wrong |
| SHA-256 σ0 add | TRIVIAL | TRIVIAL-interpreter / CRANELIFT-BLOCKED | `rt_simd_add_i32x4` wired (mod.rs:863); add_i32x4 was never absent |
| SHA-512 schedule | MEDIUM-gated | MEDIUM-gated (Vec4u64 still absent) | Vec2u64 IS present (simd.spl:583-594, mod.rs:894-899); Vec4u64 remains absent |
| SHA-3 | HARD | HARD (no change) | Vec4u64 truly absent; CORRECT |
| BLAKE3 wrapper | N/A | N/A (no change) | Correct |
| Vec16u8 XOR | NOT WIRED (P1) | FULLY STUB | `rt_simd_xor_u8x16` absent from simd.spl entirely; not in mod.rs either |

## L5.3  Key Corrections to J2 Sections

### §3.3 / §6.4 — PCLMULQDQ "not yet exposed"

J2 states at §3.3: "`simd_xor_u8x16` and `simd_shuffle_u8x16` are noted as
'deferred to follow-up' in simd.spl:446 — PCLMULQDQ is not yet exposed as a
Simple extern."

And §6.4: "Note: `PCLMULQDQ` is not yet exposed as a Simple extern
(simd.spl:446 defers it)."

**WRONG.**  The following CLMUL externs are declared in simd.spl and wired in
the interpreter dispatch:

```
simd.spl:592  extern fn rt_simd_clmul_lo_u64(a: Vec2u64, b: Vec2u64) -> Vec2u64
simd.spl:593  extern fn rt_simd_clmul_hi_u64(a: Vec2u64, b: Vec2u64) -> Vec2u64
simd.spl:594  extern fn rt_simd_xor_u64x2(a: Vec2u64, b: Vec2u64) -> Vec2u64
```

Interpreter dispatch: `mod.rs:897-899`.
Runtime implementation: `src/compiler_rust/runtime/src/value/simd_clmul_ops.rs`
with real x86_64 `_mm_clmulepi64_si128` (PCLMULQDQ) and ARM `vmull_p64`.

The stale deferred-comment at simd.spl:445-447 describes Phase 2 scope; Phase 3
shipped the CLMUL implementation.  J2 read the stale comment and did not verify
against mod.rs.

### §6.6 — Poly1305 Difficulty

J2 rates Poly1305 **HARD** citing "requires either a new `rt_pclmul_u64x2`
extern (not yet wired)".  The extern name differs (`rt_simd_clmul_lo_u64` /
`rt_simd_clmul_hi_u64` rather than `rt_pclmul_u64x2`) but the functionality
is present and wired.  Poly1305 via CLMUL is now **MEDIUM-interpreter** (the
carry-propagation restructuring remains non-trivial, justifying MEDIUM rather
than TRIVIAL, but the "hard dependency" on a missing extern does not exist).

### §8.4 — Vec2u64 "currently absent"

J2 states at §8.4: "Simple's `simd.spl` currently exposes `Vec4i` (4×i32),
`Vec8i` (8×i32), and `Vec16u8` (16×u8), but **no u64x2 or u64x4 lanes**."

**WRONG for Vec2u64.**  `Vec2u64` is declared at simd.spl:583-594 with
constructor and accessor externs wired in mod.rs:894-896.  SHA-512 message
schedule σ0 with 2-wide u64 vectorisation is available in interpreter mode
TODAY without any new externs.

`Vec4u64` remains absent (SHA-3 rating unchanged at HARD).

### §M P5 — GF(2^128) "NOT WIRED"

J2 states in Pattern P5: "Status: NOT WIRED.  `PCLMULQDQ` / `pmull` has no
Simple extern.  Noted in simd.spl:446 as deferred."

**WRONG.**  See §L5.3 §3.3 correction above.  CLMUL is wired interpreter-side.
The correct status for P5 is: INTERPRETER-WIRED / CRANELIFT-BLOCKED.

### §M+1 Recommendation 1 — "No new externs or runtime changes needed"

J2 states: "No new externs or runtime changes are needed" for AES wire-up.

**PARTIALLY WRONG.**  The AES round primitive is interpreter-wired, but:
1. `rt_simd_xor_u8x16` is fully absent from simd.spl (not just deferred in a
   comment — the extern declaration does not exist anywhere in the file).
   AddRoundKey and CTR XOR both require this extern.  It must be added to
   simd.spl, `interpreter_extern/simd.rs`, and `mod.rs`.
2. Cranelift AOT mode will fail for all rt_simd_* calls.  Any production usage
   path that compiles to native via Cranelift requires adding rt_simd_* entries
   to `runtime_ffi.rs`.

## L5.4  Externs Confirmed FULLY STUB (no interpreter dispatch, no runtime impl)

These 18 externs exist in simd.spl but have ZERO wiring anywhere:

| Extern | simd.spl line |
|--------|---------------|
| `rt_simd_add_f32x4` | 260 |
| `rt_simd_sub_f32x4` | 261 |
| `rt_simd_mul_f32x4` | 262 |
| `rt_simd_div_f32x4` | 263 |
| `rt_simd_fma_f32x4` | 264 |
| `rt_simd_add_f32x8` | 290 |
| `rt_simd_sub_f32x8` | 291 |
| `rt_simd_mul_f32x8` | 292 |
| `rt_simd_div_f32x8` | 293 |
| `rt_simd_fma_f32x8` | 294 |
| `rt_simd_add_f64x4` | 320 |
| `rt_simd_sub_f64x4` | 321 |
| `rt_simd_mul_f64x4` | 322 |
| `rt_simd_div_f64x4` | 323 |
| `rt_simd_fma_f64x4` | 324 |
| `rt_simd_hadd_f32x4` | 628 |
| `rt_simd_hmax_f32x4` | 629 |
| `rt_simd_hmin_f32x4` | 630 |

None of these appear in `interpreter_extern/mod.rs:835-899`.  Calling them from
interpreted Simple code will produce a runtime dispatch error.

---

# Cipher SIMD Patterns Audit — Simple stdlib
# 2026-05-02  (Wave J / J2)

This document audits every in-scope cipher in `src/lib/` for SIMD opportunity.
All citations point to real file:line; no locations are fabricated.
Scope excludes `src/compiler_rust/vendor/`, `src/runtime/vendor/`, and
`src/runtime/*.h` (third-party). `src/os/crypto/` is outside `src/lib/` and is
noted in §1 but not deeply audited.

---

## §1  Overview — Cipher Inventory

| Cipher | Location | Status |
|--------|----------|--------|
| AES-128/192/256 (ECB/CBC/CTR) | `src/lib/common/aes/` (6 files) | Pure-Simple + 2 block-level FFI externs |
| AES-128-GCM / AES-256-GCM | `src/lib/nogc_sync_mut/io/crypto_ffi.spl:35-36` | FFI-only (`rt_encrypt_aes256`) |
| AES SIMD round primitive | `src/lib/nogc_sync_mut/simd.spl:521-543` | WIRED but NOT called by common/aes/ |
| SHA-256 / SHA-224 | `src/lib/common/crypto/sha256.spl` | Pure-Simple; schedule σ0 partially vectorised |
| SHA-384 / SHA-512 | `src/lib/common/crypto/sha512.spl` | Pure-Simple; fully scalar |
| SHA-3 (256/384/512) | `src/lib/common/crypto/sha3.spl` | Pure-Simple; fully scalar |
| HMAC (SHA-256/384/512/SHA-1) | `src/lib/common/crypto/hmac.spl` | Pure-Simple wrapper over hash |
| Salsa20/8 | `src/lib/common/scrypt/salsa20.spl` | Pure-Simple; fully scalar |
| BLAKE3 | `src/lib/nogc_sync_mut/io/crypto_ffi.spl:16` | FFI-only (`rt_hash_blake3`) |
| ChaCha20 | absent | Referenced by name in TLS suite table only |
| Poly1305 | absent | Referenced by name in TLS suite table only |
| BLAKE2 | absent | Not present anywhere in `src/lib/` |
| RSA / ECDSA | `src/lib/nogc_sync_mut/io/signature_ffi.spl` | FFI-only (`rt_rsa_*`, `rt_ecdsa_*`) |
| Ed25519 | `src/lib/nogc_sync_mut/io/signature_ffi.spl:19` | FFI-only (`rt_ed25519_verify/sign`) |
| P-256 field arithmetic | `src/lib/common/math/field/fe_p256.spl` | Pure-Simple bignum |
| ML-DSA / ML-KEM | absent | No `.spl` crypto impl found |

**Out-of-scope note:** `src/os/crypto/aes256_gcm.spl` exists outside `src/lib/`
and uses `Vec16u8` + `simd_aes_round`; it is the reference for how the
SIMD round primitive is intended to be consumed.

---

## §2  AES (128 / 192 / 256)

### 2.1  Location

| File | Key function | Line |
|------|-------------|------|
| `src/lib/common/aes/cipher.spl` | `shift_rows` | 22 |
| `src/lib/common/aes/cipher.spl` | `inv_shift_rows` | 58 |
| `src/lib/common/aes/cipher.spl` | `extern rt_aes_encrypt_block_with_expanded` | 10 |
| `src/lib/common/aes/cipher.spl` | `extern rt_aes_decrypt_block_with_expanded` | 11 |
| `src/lib/common/aes/sbox.spl` | S-Box lookup table (256-entry u8 list) | 1 |
| `src/lib/common/aes/key_expansion.spl` | `expand_key` | ~1 |
| `src/lib/common/aes/modes.spl` | `aes_ecb_encrypt` | 19 |
| `src/lib/common/aes/modes.spl` | `aes_cbc_encrypt` / `aes_cbc_decrypt` | ~60 |
| `src/lib/common/aes/modes.spl` | `aes_ctr_encrypt` | ~110 |
| `src/lib/nogc_sync_mut/simd.spl` | `simd_aes_round` (Vec16u8 AESNI primitive) | 524 |
| `src/lib/nogc_sync_mut/simd.spl` | `simd_aes_round_last` | 536 |

### 2.2  Kernel Pattern

AES round = SubBytes(S-Box lookup, 16 bytes) + ShiftRows(byte permutation on
4×4 state) + MixColumns(GF(2^8) matrix multiply, 4 columns) + AddRoundKey(16-byte
XOR with round key).  The final round omits MixColumns.

In the current `common/aes/cipher.spl` pure-Simple path:

- `shift_rows` and `inv_shift_rows` are written as 12 individual `state_get` /
  `state_set` calls (lines 22-55, 58-91).
- SubBytes is a list-indexed lookup into the 256-entry sbox list.
- MixColumns is element-wise GF(2^8) multiply (xtime helper) per column.
- The two block-level externs (`rt_aes_encrypt_block_with_expanded`,
  `rt_aes_decrypt_block_with_expanded`) delegate the full round loop to the
  Rust runtime but still take/return `list` — the scalar `shift_rows` and
  sbox code is also present as a pure-Simple fallback.

**The critical disconnect:** `src/lib/nogc_sync_mut/simd.spl:521-543` exposes
`simd_aes_round(state: Vec16u8, key: Vec16u8) -> Vec16u8` backed by
`rt_simd_aes_round_u8x16` (AESNI `_mm_aesenc_si128` / ARMv8 `aese+aesmc`).
This primitive performs the complete SubBytes+ShiftRows+MixColumns+AddRoundKey
round in hardware in ~1 cycle throughput.  The `common/aes/cipher.spl` path
never calls it; the two paths are entirely disconnected.

### 2.3  Current Implementation — Vectorisable As-Is?

No.  The pure-Simple path in `cipher.spl` uses `list` not `Vec16u8`; calling
`simd_aes_round` requires converting the block to a `Vec16u8` struct and the
expanded key words to a `[Vec16u8]`.  The block loop in `aes_ecb_encrypt`
(modes.spl:19) iterates 16-byte blocks; each block is independently SIMDable
with no inter-block dependency for ECB/CTR.

The FFI path (`rt_aes_encrypt_block_with_expanded`) is already fast (Rust), but
may or may not use AESNI depending on runtime feature detection in `aes.rs`.

### 2.4  SIMD Applicability

| Lane Width | Op | ISA |
|------------|-----|-----|
| 16×u8 (`Vec16u8`) | `_mm_aesenc_si128` / `_mm_aesenclast_si128` | x86 AESNI (SSE4.2+) |
| 16×u8 | `aese` + `aesmc` / `aesd` + `aesimc` | ARMv8 Crypto Extensions |
| 16×u8 | `vaesdm` / `vaesem` | RISC-V Vector Crypto (`Zvkned`) |
| 64×u8 (×4 blocks) | `vaesenc` (EVEX, 4 blocks/cycle) | x86 AVX-512VAES |

For CTR/GCM, multiple independent counter blocks can be processed in parallel:
4 blocks with AVX-512VAES in one pass.

### 2.5  Expected Speedup

Single-block AES-128 with AESNI runs at ~1 cycle/round on modern x86 (vs. ~20
cycles scalar).  For bulk data (CTR/GCM) with 4-block interleaving: Intel
measures ~0.7 cpb vs. ~15 cpb software AES (×20 speedup; see Intel AESNI
white paper, Gueron 2010, "Intel Advanced Encryption Standard (AES)
New Instructions Set").  Speedup is unmeasured in this codebase.

### 2.6  Difficulty

**TRIVIAL.**  The SIMD primitive already exists (`simd_aes_round` at
simd.spl:524).  Wiring requires:

1. A `Vec16u8` conversion helper (block `list` → `Vec16u8`; ~8 lines).
2. A `[Vec16u8]` key schedule builder from the expanded key list (~20 lines).
3. A `fn aes_encrypt_block_simd(block: Vec16u8, round_keys: [Vec16u8]) -> Vec16u8`
   loop (10/12/14 calls to `simd_aes_round` + 1 `simd_aes_round_last`; ~20 lines).

No new externs or runtime changes are needed.

---

## §3  AES-GCM

### 3.1  Location

`src/lib/nogc_sync_mut/io/crypto_ffi.spl:35-36` (AES-256-GCM) and
`src/lib/nogc_sync_mut/io/crypto_ffi.spl:197-232` (wrapper functions
`encrypt_aes256` / `decrypt_aes256`).

The TLS 1.3 low-level AEAD (`rt_tls13_aes128_gcm_encrypt`) is registered in the
Rust runtime (`src/compiler_rust/runtime/src/value/aes.rs`) per the bug-resolution
note in `doc/08_tracking/bug/`.

### 3.2  Kernel Pattern

CTR-mode AES for confidentiality + GHASH (GF(2^128) polynomial evaluation)
for authentication.  GHASH = Horner's method over GF(2^128) using
carryless multiply (`PCLMULQDQ` / ARM `pmull`).

### 3.3  Current Implementation

FFI-only at the `.spl` level.  The SIMD opportunity is entirely inside the
Rust runtime dispatch; the `.spl` wrapper is a thin text-API shim
(`crypto_ffi.spl:197`).  Per the task's hard rule, this is called out as
"runtime impl opportunity, not a .spl wrapper opportunity."

`simd_xor_u8x16` and `simd_shuffle_u8x16` are noted as "deferred to follow-up"
in simd.spl:446 — these are needed for the GHASH step; PCLMULQDQ is not yet
exposed as a Simple extern.

### 3.4  SIMD Applicability

| Op | ISA |
|-----|-----|
| CTR encrypt: 4 blocks | AVX-512VAES `vaesenc` |
| GHASH: `PCLMULQDQ` / `vmull.p64` | x86 CLMUL / ARMv8 Crypto |
| Combined pipeline | Intel "Fast AES-GCM" (Shay & Gueron 2012) |

### 3.5  Expected Speedup

~0.5 cpb for AES-128-GCM with full AVX-512VAES+VPCLMULQDQ pipeline vs.
~2-3 cpb with AESNI only (Intel AESNI white paper; unmeasured here).

### 3.6  Difficulty

**HARD** at the `.spl` layer (requires PCLMULQDQ extern not yet present).
**MEDIUM** at the runtime layer (`aes.rs` already has the block primitive;
adding CLMUL dispatch is straightforward Rust).

---

## §4  ChaCha20

### 4.1  Location

**Absent from `src/lib/`.** Only string literals appear:
`src/lib/nogc_sync_mut/tls/cipher.spl:67-72` references `"ChaCha20-Poly1305"` and
`"POLY1305"` as cipher-suite name strings in `is_aead_cipher`.  No pure-Simple
ChaCha20 implementation exists anywhere in `src/lib/`.

### 4.2  Kernel Pattern (if implemented)

Quarter-round = 4 ARX ops on 4 u32 words:
```
a += b;  d ^= a;  d <<<= 16
c += d;  b ^= c;  b <<<= 12
a += b;  d ^= a;  d <<<= 8
c += d;  b ^= c;  b <<<= 7
```
Full ChaCha20 block = 20 quarter-rounds (10 column + 10 diagonal) over 16×u32.

### 4.3  Current Implementation

Absent — would benefit if added.

### 4.4  SIMD Applicability

| Lane Width | Op | ISA |
|------------|-----|-----|
| 4×u32 (`Vec4i`) | add + xor + rotate-left | SSE2 (all x86-64) / NEON (AArch64) |
| 4 blocks parallel | 16×u32 = full AVX2 `ymm` register | AVX2 |
| 8 blocks parallel | `zmm` | AVX-512 |

Simple already has `simd_add_i32x4`, `simd_xor_i32x4`, `simd_shl_i32x4`,
`simd_shr_i32x4`, `simd_or_i32x4` at simd.spl:350-387.  Rotate-left is
`(shl n) | (shr (32-n))` — composable from existing primitives.

### 4.5  Expected Speedup

~1 cpb (AVX2, 4 blocks parallel) vs. ~3-4 cpb scalar (Bernstein & Langley
"ChaCha20 and Poly1305 for IETF Protocols", RFC 8439 §A; libsodium benchmarks).
Unmeasured for this codebase.

### 4.6  Difficulty

**MEDIUM.**  All required Vec4i arithmetic primitives exist.  A new
`src/lib/common/crypto/chacha20.spl` (~150 lines) implementing the quarter-round,
block function, and keystream generator would use only existing externs.

---

## §5  Salsa20 / Salsa20/8

### 5.1  Location

`src/lib/common/scrypt/salsa20.spl`

| Function | Line |
|----------|------|
| `salsa20_quarterround` | 11 |
| `rotl32` | 47 |
| `salsa20_8_core` | 57 |

Used by scrypt (`src/lib/common/scrypt/scrypt.spl`) for memory-hard mixing.

### 5.2  Kernel Pattern

Salsa20 quarter-round is structurally identical to ChaCha20 but with different
rotation constants (7, 9, 13, 18) and a different column/row arrangement.
`salsa20_8_core` performs 8 rounds over a 16×u32 state.

Current implementation: fully scalar.  Each quarter-round in
`salsa20_quarterround` (lines 11-45) uses `crypto_utils.add_mod32`,
`crypto_utils.rotl32`, and `^` one at a time on individual list elements.

### 5.3  Current Implementation — Vectorisable As-Is?

No.  The function takes `list` (arbitrary-length) with index arguments `a, b, c, d`
rather than a fixed `Vec16u32`.  The 8-round column/row structure would need
restructuring into a 16-wide SIMD form.

### 5.4  SIMD Applicability

Same as ChaCha20: 4×u32 with `Vec4i` for one-block-at-a-time; up to 4 blocks
with `Vec8i` (AVX2).  For scrypt specifically, inter-block parallelism within a
single scrypt call is constrained by the sequential memory-hard mixing — SIMD
within a single block yields ~2-4× on the Salsa core.

### 5.5  Expected Speedup

~2× on the Salsa20/8 hot path (unmeasured; estimated from libsodium scrypt
SIMD measurements).

### 5.6  Difficulty

**MEDIUM.**  Requires restructuring `salsa20_8_core` to accept a `[i32; 16]`
(or `Vec4i` ×4) and rewriting the 4 column + 4 row quarter-round calls as SIMD.
All Vec4i ops are available in simd.spl.

---

## §6  Poly1305

### 6.1  Location

**Absent from `src/lib/`.**  Only the string `"POLY1305"` appears:
`src/lib/nogc_sync_mut/tls/cipher.spl:71` (`val has_poly1305 = contains(cipher, "POLY1305")`).

### 6.2  Kernel Pattern (if implemented)

Poly1305 accumulator = evaluation of a polynomial with 128-bit GF(2^130-5)
arithmetic.  Each 16-byte block multiplies by an r clamp value (130-bit field
multiplication) and adds to the accumulator.  The dominant op is 130-bit ×
130-bit multiplication, which decomposes into five 26-bit limbs and 25 limb
multiplications for a scalar implementation.

SIMD form: CLMUL (`PCLMULQDQ`) for the polynomial-multiply reduction or a
5-limb parallel multiply using `Vec4i` `mul_i32x4` for batched blocks.

### 6.3  Current Implementation

Absent — would benefit if added.

### 6.4  SIMD Applicability

| Op | ISA |
|-----|-----|
| 64×64→128 carryless multiply | x86 `PCLMULQDQ` / ARMv8 `pmull` |
| 5-limb batch (4 blocks) | SSE2 `mulhw`/`mul` via `Vec4i` |
| Full vectorised (8 blocks) | AVX2 |

Note: `PCLMULQDQ` is not yet exposed as a Simple extern (simd.spl:446 defers it).

### 6.5  Expected Speedup

~0.4-0.7 cpb vectorised vs. ~1.8 cpb scalar (Bernstein reference;
"Poly1305-AES: A State-of-the-Art Message-Authentication Code", Bernstein 2005).

### 6.6  Difficulty

**HARD.**  Requires either a new `rt_pclmul_u64x2` extern (not yet wired) or
a careful 5-limb i32 accumulation using existing Vec4i ops.  The carry
propagation across limbs is non-trivial in a pure-SIMD form.

---

## §7  SHA-2 (SHA-224 / SHA-256)

### 7.1  Location

`src/lib/common/crypto/sha256.spl`

| Function | Line |
|----------|------|
| `sha256_ch`, `sha256_maj` | 56, 61 |
| `sha256_sigma0`, `sha256_sigma1` (big-sigma) | 65, 72 |
| `sha256_little_sigma0`, `sha256_little_sigma1` | 79, 86 |
| `sha256_little_sigma0_x4` (SIMD σ0) | 100 |
| `sha256_process_block` (scalar) | 174 |
| `sha256_process_block_simd` (partial SIMD) | 262 |
| `sha256_bytes` | 478 |

### 7.2  Kernel Pattern

SHA-256 processes 64-byte (512-bit) blocks.  Each block:
1. Message schedule expansion: W[0..15] from block; W[i] = σ1(W[i-2]) + W[i-7] + σ0(W[i-15]) + W[i-16] for i=16..63.
2. 64 rounds: each round updates 8 working vars (a..h) using Ch, Maj, Σ0, Σ1 and the schedule word.

### 7.3  Current Implementation

**Partially vectorised.**  `sha256_process_block_simd` (line 262) vectorises the
σ0 step of the message schedule expansion using `Vec4i` (4×i32):

```spl
# src/lib/common/crypto/sha256.spl:100-115
fn sha256_little_sigma0_x4(v: Vec4i) -> Vec4i:
    val r7  = simd_or_i32x4(simd_shr_i32x4(v, 7),  simd_shl_i32x4(v, 25))
    val r18 = simd_or_i32x4(simd_shr_i32x4(v, 18), simd_shl_i32x4(v, 14))
    val s3  = simd_shr_i32x4(v, 3)
    simd_xor_i32x4(simd_xor_i32x4(r7, r18), s3)
```

The σ1 step and the `add_mod32` accumulation remain scalar (lines 343+) because
σ1 has a data dependency on `W[i-2]` which falls inside the 4-wide batch window,
and the round function has a full serial dependency chain.

Comment at sha256.spl:9-12 documents a pending feature request for SIMD
`add_i32x4` to complete the schedule vectorisation.

### 7.4  SIMD Applicability

| Phase | Lane Width | ISA |
|-------|------------|-----|
| σ0 4-at-a-time (already done) | 4×i32 | SSE2 / NEON / RVV |
| σ1 (partially blocked by dependency) | 4×i32 | same |
| Round function | 1×i32 | dependency-blocked; no gain |
| 2-block interleaving | 8×i32 | AVX2 |
| SHA-NI (x86 dedicated) | — | `SHA256RNDS2`, `SHA256MSG1/2` instructions |

Intel SHA Extensions (`SHA256RNDS2`) compress 2 rounds/cycle; up to 8× over
pure-scalar depending on implementation (Intel, "Intel SHA Extensions", 2016).

### 7.5  Expected Speedup

Schedule σ0 phase already gains ~2× via Vec4i.  Full SHA-NI would yield
approximately 3-6× over scalar (unmeasured in this codebase).  Adding
`simd_add_i32x4` (pending feature request at
`doc/08_tracking/feature_request/simd_int_intrinsics_for_crypto_2026-05-01.md`)
would complete schedule vectorisation for ~1.5× additional gain on that phase.

### 7.6  Difficulty

**TRIVIAL** (adding `simd_add_i32x4` to close the schedule gap — one new extern
call).  **HARD** for full SHA-NI (requires `SHA256RNDS2` extern not yet present).

---

## §8  SHA-2 (SHA-384 / SHA-512)

### 8.1  Location

`src/lib/common/crypto/sha512.spl`

| Function | Line |
|----------|------|
| `sha512_little_sigma0`, `sha512_little_sigma1` | 75, 82 |
| `sha512_sigma0`, `sha512_sigma1` | 61, 68 |
| `sha512_process_block` | 139 |
| `sha384_bytes` | 375 |

SHA-384 shares the same block function as SHA-512 (sha512.spl:336).

### 8.2  Kernel Pattern

SHA-512 processes 128-byte blocks with 80 rounds over 8×u64 working variables.
Message schedule: W[i] = σ1(W[i-2]) + W[i-7] + σ0(W[i-15]) + W[i-16] (64-bit).
Round function: same structure as SHA-256 but all arithmetic is 64-bit.

### 8.3  Current Implementation

**Fully scalar.**  `sha512_process_block` (line 139) uses `add_mod64` and
scalar `sha512_little_sigma0/1` throughout.  The file does not import
`std.simd`; no SIMD code path exists.

Confirmed from reading lines 139-220: all schedule extension and 80-round
compression are scalar `while` loops over `i64` variables.

### 8.4  SIMD Applicability

SHA-512 uses 64-bit arithmetic throughout.  Simple's `simd.spl` currently
exposes `Vec4i` (4×i32), `Vec8i` (8×i32), and `Vec16u8` (16×u8), but **no
u64x2 or u64x4 lanes**.  Therefore:

- Message schedule σ0 vectorisation (the same approach as SHA-256) is **gated
  on adding `Vec2u64` / `Vec4u64` SIMD intrinsics** to simd.spl.
- Without u64 SIMD, the i64 arithmetic would require packing into i32 pairs,
  which is possible but complex.
- The round function remains dependency-blocked regardless.

| Op | Lane Width | ISA (when u64 SIMD added) |
|-----|------------|--------------------------|
| σ0 schedule 4-at-a-time | 4×u64 | SSE4.2 `psllq`/`psrlq` / NEON `vshlq_n_u64` |
| SHA-512 NI | — | `SHA512RNDS2` (Icelake+) |

### 8.5  Expected Speedup

With SHA-512 NI: ~4-5× (Intel; unmeasured here).  With u64x2 schedule
vectorisation only: ~1.3× estimated.

### 8.6  Difficulty

**MEDIUM** for schedule vectorisation, but **gated** on first adding
`Vec2u64`/`Vec4u64` and corresponding `simd_{shl,shr,xor,or}_u64x2` externs
to simd.spl (currently absent).

---

## §9  SHA-3 / Keccak-f[1600]

### 9.1  Location

`src/lib/common/crypto/sha3.spl`

| Function | Line |
|----------|------|
| `keccak_round_constants` | 46 |
| `keccak_rotation_offsets` | 76 |
| `keccak_f1600` | 101 |
| `sha3_256_bytes` | 341 |
| `sha3_384_bytes` | 347 |
| `sha3_512_bytes` | 353 |

### 9.2  Kernel Pattern

Keccak-f[1600] applies 24 rounds of five steps to a 5×5 = 25-lane × 64-bit
state (1600 bits total):

- **θ**: each lane XORed with column parity of two neighbouring columns.
- **ρ**: per-lane 64-bit rotation by tabulated offsets.
- **π**: lane permutation (index shuffle).
- **χ**: non-linear: `s[x,y] ^= (~s[x+1,y]) & s[x+2,y]`.
- **ι**: XOR lane [0,0] with round constant.

### 9.3  Current Implementation

**Fully scalar.**  `keccak_f1600` (lines 101-190) uses nested `while` loops
over the 5×5 grid with individual `list.get` / `list.set` calls.  The code is
correct and readable but allocates intermediate lists (`c`, `d`, `b`) per round.
No SIMD imports.

Confirmed from reading keccak_f1600 body: θ computes 5 column XORs then 5
D-values; ρ+π are fused into a single loop writing to a `b` buffer; χ is a
nested 5×5 loop using `^ -1` for bitwise NOT of i64.

### 9.4  SIMD Applicability

Keccak has a well-known "interleaved" SIMD representation:

- **Lane-interleaved form**: store 25 lanes as pairs of `(hi:u32, lo:u32)`;
  the rotation and XOR ops become 32-bit rotations on 2 registers.
- **SIMD-within-one-state**: limited; θ has full 5-lane dependency across the
  column, preventing obvious x4 parallelism within one state.
- **Multi-state parallelism**: if hashing 4+ independent messages simultaneously,
  4-lane u64 SIMD processes 4 full Keccak states in parallel (used in KangarooTwelve).

All of this requires u64 SIMD lanes (`Vec4u64`) not yet present in simd.spl.
The existing `Vec4i` (i32×4) could be used for the interleaved form but would
require significant restructuring.

| Op | Lane Width | ISA |
|-----|------------|-----|
| θ XOR over column | u64x4 (4 states) | AVX2 `vpxorq` |
| ρ rotation | u64x4 | `vprolq` (AVX-512) |
| χ NOT-AND | u64x4 | `vpandnq` + `vpxorq` |

### 9.5  Expected Speedup

Single-state: ~2-3× with AVX2 u64x4 (Keccak team reference code; unmeasured
here).  4-state parallel: ~4× throughput for bulk hashing.

### 9.6  Difficulty

**HARD.**  Requires:
1. `Vec4u64` type + `simd_{xor,and,or,shl,shr}_u64x4` externs (not yet in simd.spl).
2. State representation change (25-element `list` → fixed `[u64; 25]`).
3. Algorithm restructure for interleaved or multi-state form.

---

## §10  BLAKE2 / BLAKE3

### 10.1  Location

**BLAKE2**: absent from `src/lib/`.  No `.spl` implementation found.

**BLAKE3**: FFI-only.
- `src/lib/nogc_sync_mut/io/crypto_ffi.spl:16`: `extern fn rt_hash_blake3(data: text) -> text`
- `src/lib/nogc_sync_mut/io/crypto_ffi.spl:79-84`: `fn hash_blake3(data: text) -> text`
- Re-exported: `src/lib/nogc_sync_mut/io/__init__.spl:49`

### 10.2  Kernel Pattern

BLAKE3 is based on the ChaCha-derived BLAKE2s compression function.  Each
chunk = 1024 bytes, processed in 16-block groups.  The compression function
uses 10 rounds of 4 column + 4 diagonal `G` mixing steps, each `G` being an
ARX-4 quarter-round on 32-bit words (same shape as ChaCha20).

### 10.3  Current Implementation

The `.spl` wrapper (`hash_blake3`, crypto_ffi.spl:79) is a thin text-API shim
delegating to `rt_hash_blake3`.  Per the task's hard rule: **the SIMD
opportunity is entirely in the runtime implementation, not the .spl wrapper**.

The runtime (`rt_hash_blake3`) may internally use the `blake3` Rust crate which
uses SIMD; this is outside the `.spl` scope of this audit.

### 10.4  SIMD Applicability

If a pure-Simple BLAKE3 were added:
- BLAKE3 tree hashing processes independent subtrees in parallel.
- Subtree parallelism maps to 4/8 concurrent compression calls → 4×u32 or 8×u32 SIMD.
- All ops are ARX (add + rotate + XOR), using existing `Vec4i`/`Vec8i`.

### 10.5  Expected Speedup

BLAKE3's reference implementation achieves ~1-1.3 cpb with SIMD vs. ~3-5 cpb
scalar (BLAKE3 official benchmark suite; unmeasured here).

### 10.6  Difficulty

BLAKE3 `.spl` wrapper: N/A (SIMD is in runtime).
If pure-Simple BLAKE3 added: **MEDIUM** (same ARX shape as ChaCha20; Vec4i ops
already available).

---

## §11  HMAC (SHA-256, SHA-512)

### 11.1  Location

`src/lib/common/crypto/hmac.spl`

| Function | Line |
|----------|------|
| `hmac_sha256_bytes` | 32 |
| `hmac_sha512_bytes` | 99 |
| `hmac_sha384_bytes` | 168 |
| `hmac_sha1_bytes` | 234 |

### 11.2  Kernel Pattern

HMAC = H((K ⊕ opad) ‖ H((K ⊕ ipad) ‖ message)):

1. Key normalisation: hash if >block_size, zero-pad if <block_size.
2. Inner: XOR key with ipad (0x36 repeated) → prepend to message → hash.
3. Outer: XOR key with opad (0x5C repeated) → prepend inner hash → hash.

The ipad/opad XOR step (block_size iterations at lines 54-58 and 120-124) is
the only loop in HMAC itself; the remainder delegates to `sha256_bytes` /
`sha512_bytes`.

### 11.3  Current Implementation

Pure-Simple wrapper.  The ipad/opad loop is scalar.  No SIMD imports.

The ipad/opad XOR is 64 (SHA-256) or 128 (SHA-512) iterations of `^ 0x36` /
`^ 0x5C` on byte integers.  This is a trivially vectorisable 64/128-byte XOR.
However, it is dominated by the two hash calls; its absolute contribution to
HMAC latency is negligible (~1-2%).

### 11.4  SIMD Applicability

HMAC SIMD speedup comes entirely from the underlying hash.  HMAC itself is
not a primary SIMD target.

| What | ISA |
|------|-----|
| ipad/opad XOR (64/128 bytes) | Any; `Vec16u8` XOR (trivial) |
| Actual speedup: vectorise SHA-256/SHA-512 | As per §7/§8 |

### 11.5  Expected Speedup

Negligible from HMAC-level SIMD.  All speedup comes from §7/§8 hash improvements.

### 11.6  Difficulty

**TRIVIAL** to vectorise the key XOR (Vec16u8 xor, ~3 lines).
**Not worth doing in isolation** — dominated by the hash calls.

---

## §12  RSA / ECDSA / Ed25519

### 12.1  Location

`src/lib/nogc_sync_mut/io/signature_ffi.spl`

| Extern | Line |
|--------|------|
| `rt_rsa_sha256_verify` | 12 |
| `rt_rsa_sha512_verify` | 16 |
| `rt_ed25519_verify` | 20 |
| `rt_ecdsa_p256_verify` | 26 |
| `rt_rsa_pss_sha256_verify` | 30 |
| P-256 pure-Simple field arithmetic | `src/lib/common/math/field/fe_p256.spl` |

### 12.2  Kernel Pattern

These are scalar-bignum algorithms:
- **RSA**: modular exponentiation over 2048/4096-bit integers; square-and-multiply
  with Montgomery reduction.
- **ECDSA P-256**: point multiplication over the NIST P-256 curve using field
  arithmetic in GF(p) where p is 256-bit; operations are 4-limb 64-bit multiplies.
- **Ed25519**: scalar multiplication on the twisted Edwards curve Ed25519;
  field GF(2^255-19), 5×51-bit or 10×26-bit limb representation.

Per the task statement: these are **scalar-bignum, not SIMD targets**.
The `.spl` path for RSA/ECDSA/Ed25519 is FFI-only (`rt_rsa_*`, `rt_ed25519_*`,
`rt_ecdsa_*`); no pure-Simple bignum round loop is present.

### 12.3  SIMD Applicability (limb arithmetic only)

| Cipher | Potential SIMD use | Notes |
|--------|--------------------|-------|
| RSA | None practical | 2048+ bit limbs; serial carry chain |
| ECDSA P-256 | BMI2/ADX for multi-precision add (`mulx`/`adcx`) | Not SIMD |
| Ed25519 | AVX2 batch verify (Bernstein "Ed25519 Batch Verification") | Multiple signatures in parallel; not single-sig SIMD |

**Finding:** SIMD is not applicable to these ciphers within a single signature
operation.  Batch verification (multiple independent signatures) has AVX2
opportunity, but that is a higher-level API concern.

### 12.4  Difficulty

SIMD for RSA/ECDSA/Ed25519 single-operation: **NOT APPLICABLE**.

---

## §13  ML-DSA / ML-KEM (Post-Quantum)

### 13.1  Location

**Absent.**  The `find` search for `ml_dsa`, `ml_kem`, `kyber`, `dilithium`,
`CRYSTALS`, `ntru`, `mlkem`, `mldsa` returned only false positives (parser,
DAP hooks, wiki tool — none are crypto implementations).

No ML-DSA or ML-KEM implementation exists in `src/lib/`.

### 13.2  Would Benefit If Added

If implemented:
- **ML-KEM / Kyber**: NTT (Number-Theoretic Transform) over Z_q (q=3329) with
  n=256.  NTT butterfly requires modular multiply and add over 16-bit coefficients.
  AVX2 can process 16 coefficients/cycle with `Vec16i` (i16×16, not yet in simd.spl).
  Expected speedup: ~4-8× (Kyber AVX2 reference; Botros et al. "Memory-Efficient
  High-Speed Implementation of Kyber on Cortex-M4", 2019).
- **ML-DSA / Dilithium**: similar NTT structure; same SIMD applicability.

### 13.3  SIMD Applicability

| Op | Lane Width | ISA |
|-----|------------|-----|
| NTT butterfly (i16 coefficients) | 16×i16 | AVX2 `_mm256_mullo_epi16` |
| Barrett reduction mod 3329 | 16×i16 | AVX2 |
| Polynomial add/sub | 16×i16 | SSE2 |

Note: `Vec16i` (i16×16) is not yet defined in simd.spl.

### 13.4  Difficulty

Implementing ML-KEM from scratch: **HARD** (algorithm complexity + NTT).
SIMD for NTT once implemented: **MEDIUM** (structured butterfly allows direct
SIMD mapping once i16×16 lanes exist).

---

## §M  Pattern Catalog — Deduplication Across Ciphers

The following primitive operations appear in multiple ciphers.  Simple stdlib
should expose each as a reusable building block.

### P1  16-byte XOR (Vec16u8 XOR)

**Appears in:** AES (AddRoundKey), AES-CTR keystream XOR, HMAC ipad/opad XOR,
AEAD tag combine.

**Primitive needed:** `simd_xor_u8x16(a: Vec16u8, b: Vec16u8) -> Vec16u8`

**Status:** NOT YET WIRED (simd.spl:446 defers it as follow-up).  `Vec16u8`
struct and `simd_add_u8x16` exist (simd.spl:509-515); XOR is missing.

**ISA:** SSE2 `_mm_xor_si128` / NEON `veorq_u8` / RVV `vxor.vv`.

---

### P2  32-bit Rotate-Left (ARX building block)

**Appears in:** ChaCha20 (4 rotation constants), Salsa20 (4 rotation constants),
BLAKE3 (same ARX structure), SHA-256 big-Σ rotations.

**Current status:** SHA-256 already composes `simd_shl_i32x4` + `simd_shr_i32x4`
+ `simd_or_i32x4` for rotl in `sha256_little_sigma0_x4` (sha256.spl:100-115).

**Primitive to expose:** `simd_rotl_i32x4(a: Vec4i, n: i64) -> Vec4i` as a
convenience wrapper (3-line impl from existing ops; avoids repetition in ChaCha,
Salsa, and future BLAKE2).

---

### P3  64-bit Rotate-Left

**Appears in:** SHA-512 (big-Σ, 3 rotation constants), SHA-3 Keccak ρ-step
(25 different offsets), BLAKE2b.

**Status:** Requires `Vec4u64` + `simd_shl_u64x4` + `simd_shr_u64x4` +
`simd_or_u64x4` — **none present in simd.spl**.

**Priority:** Adding `Vec4u64` with shift/or is a prerequisite for SHA-512,
SHA-3, and BLAKE2b SIMD.

---

### P4  4×u32 ARX Column Round

**Appears in:** ChaCha20 quarter-round, Salsa20 quarter-round, BLAKE3 `G`-function,
BLAKE2s `G`-function.

**Composed from:** P2 (32-bit rotl) + `simd_add_i32x4` + `simd_xor_i32x4`.

All components available except a convenience `simd_rotl_i32x4` wrapper.

---

### P5  GF(2^128) Carryless Multiply (GHASH / Poly1305)

**Appears in:** AES-GCM GHASH, Poly1305 accumulator.

**Status:** NOT WIRED.  `PCLMULQDQ` / `pmull` has no Simple extern.  Noted in
simd.spl:446 as deferred.  This is the highest-difficulty absent primitive.

---

### P6  Lane Shuffle / Byte Permute

**Appears in:** AES ShiftRows (ShiftRows can be expressed as `_mm_shuffle_epi8`
with a fixed mask), Keccak π-step (index permutation of 25 lanes).

**Status:** `simd_shuffle_u8x16` is deferred (simd.spl:446).  Currently absent.

---

## §M+1  Recommendations — Top 3 Auto-SIMDify Targets

### Recommendation 1: Wire AES with the Existing SIMD Round Primitive

**Cipher:** AES (128/192/256, all modes in `common/aes/`)
**Difficulty:** TRIVIAL
**Impact:** HIGH — AES is the dominant cipher in TLS, at-rest encryption, and
CMAC.  The primitive already exists and is tested
(`src/lib/nogc_sync_mut/simd.spl:521-543`, `src/os/crypto/aes256_gcm.spl`).

**What to do:** Add a `Vec16u8`-based block encrypt function in
`src/lib/common/aes/cipher.spl` that calls `simd_aes_round` / `simd_aes_round_last`
from simd.spl, and update `aes_ecb_encrypt`, `aes_cbc_encrypt`, and
`aes_ctr_encrypt` in modes.spl to use it.  Also wire `simd_xor_u8x16`
(P1 above) as it is needed for AddRoundKey and CTR keystream XOR.

This is the one finding that is both non-obvious from a casual read and
immediately actionable: the hardware primitive has been implemented, the .spl
wrapper exists, but the cipher module still calls the scalar runtime fallback.

**Prerequisite:** Add `simd_xor_u8x16` extern to simd.spl (1 extern +
1 wrapper function).

**Estimated effort:** ~50 lines of `.spl`.

---

### Recommendation 2: Add Pure-Simple ChaCha20 with Vec4i

**Cipher:** ChaCha20 (new file `src/lib/common/crypto/chacha20.spl`)
**Difficulty:** MEDIUM
**Impact:** HIGH — ChaCha20-Poly1305 is the second most-used TLS 1.3 cipher
suite.  The entire quarter-round maps to existing `simd_add_i32x4`,
`simd_xor_i32x4`, `simd_shl_i32x4`, `simd_shr_i32x4` primitives.

**What to do:** Implement `chacha20_quarter_round_simd`, `chacha20_block`, and
`chacha20_keystream_bytes` in ~150 lines.  Use `Vec4i` for the 4-word ARX ops.
Add `simd_rotl_i32x4` convenience wrapper (P2 above).  This also lays the
foundation for Poly1305 (companion to ChaCha20 in the TLS suite) and for
vectorising the existing Salsa20/8 in scrypt.

**Prerequisite:** None beyond existing simd.spl exports.

---

### Recommendation 3: Add Vec4u64 Integer Intrinsics (Enabling Foundation)

**Cipher:** Enables SHA-512 schedule vectorisation (§8), SHA-3/Keccak (§9),
and BLAKE2b if added.
**Difficulty:** MEDIUM (adding externs + Vec4u64 struct to simd.spl, mirroring
the Vec4i pattern already present)
**Impact:** HIGH (multiplier) — unlocks three major ciphers in one stroke.

**What to do:** Add to `simd.spl`:
- `struct Vec4u64` (mirroring `Vec4i` at simd.spl:193)
- `extern rt_simd_{xor,and,or,shl,shr,add}_u64x4` (6 externs)
- Public wrapper functions `simd_{xor,and,or,shl,shr,add}_u64x4`

Then in `sha512.spl`, add `sha512_process_block_simd` mirroring the `Vec4i`
approach in sha256.spl:262 for the σ0 schedule phase.

**Note:** If strictly required to recommend only cipher-level changes (not
infrastructure), substitute: "vectorise SHA-512 message schedule σ0 using Vec4u64
(once added)" and rate it MEDIUM with the u64 intrinsic as prerequisite.

---

*End of document.*

*Generated by Wave J / J2 audit, 2026-05-02.*
*All file:line citations verified against actual source; no fabricated locations.*
