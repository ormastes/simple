# Security Extension Instruction Optimization — Architecture Analysis

## Summary

Security/crypto extension instructions (x86 AES-NI, ARM Crypto, RISC-V Zvk) are applied
in the **same optimization layer** as SIMD (`60.mir_opt`), gated by the same `TargetCaps`
trait and `TargetFeatureClass` enum — but via a fundamentally **different detection mechanism**.

---

## Detection Mechanism Comparison

| Aspect | SIMD (Auto-Vectorization) | Crypto (Pattern-Idiom) |
|--------|---------------------------|------------------------|
| Detection | Loop-structure analysis (dependency, stride-1 access) | Callee-symbol name matching |
| Pass files | `auto_vectorize*.spl` (4 phases: analysis → validate → cost → codegen) | `pattern/rules_crypto.spl` + `pattern_dispatch.spl` |
| Trigger | ANY matching loop pattern (no explicit programmer intent) | Call to known stdlib symbol (e.g. `std.common.aes.cipher.aes_round_software`) |
| Gate | `TargetCaps.supports(SimdI32x4)` etc. | `TargetCaps.supports(AesEnc)` etc. |
| Rewrite | Scalar loop → vector loop (loop peeling, alignment) | `Call(dest, func, args)` ��� `Intrinsic(dest, name, args)` |
| Dispatch key | `"vectorization"` | `"pattern_idiom"` |

Both converge at the backend: `MirInstKind.Intrinsic` → byte encoder (`encode_x86_64_crypto.spl`, `encode_rvv_zvk.spl`, etc.)

---

## Industry Contrast (LLVM/GCC)

**No production compiler has "auto-cryptoization."**

| Support Level | LLVM/GCC | Simple Compiler |
|---------------|----------|-----------------|
| Inline assembly | Yes | Yes (extern) |
| Compiler intrinsics/builtins | Yes (`_mm_aesenc_si128`, `__builtin_riscv_aes64es`) | Yes (extern + MIR intrinsic) |
| Library-level dispatch | Yes (OpenSSL CPUID → asm) | Yes (cfg-gated stdlib) |
| **Automatic recognition** | **No** — intractable | **Yes** — callee-name matching of own stdlib |

Why LLVM can't: detecting that arbitrary XOR/shift/table-lookup code implements Rijndael is
equivalent to program equivalence checking (undecidable in general). Simple can because it
controls the stdlib naming — the pattern table is a finite lookup of known symbols, not
semantic analysis.

This is analogous to LLVM's `sin()`/`cos()` → platform math intrinsic folding, but applied
to crypto operations.

---

## Architecture in the Simple Compiler

```
┌─────────────────────────���───────────────────────────────────────┐
│ 60.mir_opt  — Unified Optimization Layer                        │
│                                                                 │
│  ┌───────────────────────┐    ┌──────────────────────────────┐  │
│  │ Auto-Vectorize        │    │ Pattern-Idiom Dispatch        │  │
│  ��� (loop detection)      │    ��� (callee-name matching)        │  │
│  │                       │    │                               │  │
│  │ → analyze deps        │    │ → lookup_rule_for_callee()    │  │
│  │ → validate            │    │ → idiom_for_intrinsic()       │  │
│  │ → cost model          │    │ → caps.supports(idiom)?       │  │
│  │ → codegen             │    │ → rewrite Call → Intrinsic    │  │
│  └───────────┬───────────┘    └──────────────┬───────────────┘  │
│              │                                │                  │
│              └──────────┬─────────────────────┘                  │
│                         ▼                                        │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │ TargetCaps trait (supports / cost / preferred_vector_width)│  │
│  │   ├── X86Caps     (AES-NI, SHA-NI, SSE4.2, AVX2, AVX512)│  │
│  │   ├── Aarch64Caps (AES, SHA2, SHA3, PMULL, CRC32, SVE2) │  │
│  │   └── Rv64Caps    (Zvkned, Zvknh, Zvkg, Zbb, Zbkb, V)   │  │
│  └────────────────��──────────────────────��──────────────────┘   ���
│                                                                 │
│  TargetFeatureClass enum: FixedWidthSimd | ScalableSimd |       │
│                           BitManip | Crypto | Matrix            │
└─────────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌────────────────────────────��────────────────────────────────────┐
│ 70.backend  — Target-Specific Lowering + Byte Encoding          │
│                                                                 │
│  ├── encode_x86_64_crypto.spl  (AES-NI / SHA-NI / CRC32 / PCLMUL) │
│  ├── encode_rvv_zvk.spl        (vaesef / vsha2ms / vghsh)      │
│  ├── encode_x86_64_sse41.spl   (SIMD fixed-width)              │
│  ├── encode_rvv_fixedpt.spl    (RVV SIMD)                      │
���  ├── intrinsic_lowering_aarch64.spl                             │
│  └── intrinsic_lowering_riscv.spl                               │
└──────���──────────────────────────────────────────────────────────┘
```

---

## Currently Recognised Crypto Symbols (rules_crypto.spl)

| Symbol | Intrinsic | Required Feature | Cost Delta |
|--------|-----------|------------------|------------|
| `std.common.aes.cipher.aes_round_software` | `crypto_aes_round` | `aes` | -3 |
| `std.common.aes.cipher.aes_round_last_software` | `crypto_aes_round_last` | `aes` | -3 |
| `std.common.aes.cipher.aes_inv_round_software` | `crypto_aes_inv_round` | `aes` | -3 |
| `std.common.aes.cipher.aes_inv_round_last_software` | `crypto_aes_inv_round_last` | `aes` | -3 |
| `std.common.aes.cipher.aes_imc_software` | `crypto_aes_imc` | `aes` | -2 |
| `std.common.aes.cipher.aes_keygen_assist_software` | `crypto_aes_keygen_assist` | `aes` | -2 |
| `std.common.crypto.sha256.compress_block` | `crypto_sha256_rounds2` | `sha2` | -8 |
| `std.common.crypto.sha256.msg_schedule1` | `crypto_sha256_msg1` | `sha2` | -4 |
| `std.common.crypto.sha256.msg_schedule2` | `crypto_sha256_msg2` | `sha2` | -4 |
| `std.common.crypto.crc32.update_byte` | `crc32_u8` | `crc32` | -2 |
| `std.common.crypto.crc32.update_u32` | `crc32_u32` | `crc32` | -2 |
| `std.common.crypto.crc32.update_u64` | `crc32_u64` | `crc32` | -3 |
| `std.common.crypto.clmul.clmul_lo` | `clmul_lo` | `pclmul` | -5 |
| `std.common.crypto.clmul.clmul_hi` | `clmul_hi` | `pclmul` | -5 |

---

## Current Gaps

### 1. Generic Pattern Dispatch Exists; Per-Target Lowering Still Has Gaps

`pattern_dispatch.spl` now exposes a generic MIR rewrite entry point keyed by
`TargetCapsKind`, so x86, AArch64, and RV64 can all rewrite recognised crypto
and bit-idiom calls into MIR intrinsics before backend lowering.

What still remains target-specific is the intrinsic lowering depth after that
rewrite:
- x86 `bit_clz` / `bit_ctz` still return `no-cap` pending explicit `lzcnt` /
  `tzcnt` feature modeling and zero-input semantics.
- AArch64 generic `bit_popcount` still does not lower through the portable
  intrinsic-lowering path, even though native ISel now has a concrete scalar
  fallback.
- `matrix_*` idioms are recognised but still intentionally return
  `unimplemented`.

### 2. Pass-Key Separation Is Partially Complete

Crypto idiom rewriting no longer rides the shared `"vectorization"` pass key;
it now runs under `"pattern_idiom"`.

Remaining follow-up:
- auto-vectorization still uses the legacy `"vectorization"` name internally
  in some docs and comments
- a future split into `"auto_vectorize"`, `"crypto_idiom"`, and `"bit_idiom"`
  may still be worthwhile if finer-grained pass toggles are needed

### 3. Missing Algorithm Coverage

| Algorithm | x86 ISA | ARM ISA | RISC-V ISA | Rule Exists |
|-----------|---------|---------|------------|-------------|
| AES | AES-NI | AESE/AESD | Zvkned | Yes |
| SHA-256 | SHA-NI | SHA256H | Zvknh | Yes |
| CRC32 | SSE4.2 | CRC32 | — | Yes |
| CLMUL/GHASH | PCLMULQDQ | PMULL | Zvkg | Yes |
| SHA-512 | — | SHA512H | Zvknh | **No** |
| SHA-3/Keccak | — | SHA3 (EOR3) | — | **No** |
| SM3 | — | — | Zvksh | **No** |
| SM4 | — | — | Zksed | **No** |
| ChaCha20 | (AVX2 vectorize) | (NEON vectorize) | — | **No** |
| Poly1305 | (CLMUL assist) | (PMULL assist) | (Zvkg) | **Partial** (via CLMUL) |

### 4. Bit-Manipulation and SIMD Follow-On Work

Several back-end-facing blockers remain intentionally open outside this sync:
- masked / predicated MIR ops are still incomplete
- reduction vectorization is still analysis/logging-heavy rather than full
  lowering
- bulk-copy SIMD is still blocked on array-layout/runtime preconditions

### 5. Bit-Manipulation Idioms (TargetIdiom exists, no stdlib symbol rules)

`RotateLeft`, `RotateRight`, `Popcount`, `CountLeadingZeros`, `CountTrailingZeros`,
`ByteSwap`, `BitReverse` have `TargetIdiom` variants and cost entries but no entries
in `rules_crypto.spl`. These need stdlib symbol bindings.

---

## Extension Plan

### Phase 1: Finish Post-Rewrite Lowering Coverage

1. Add explicit x86 `lzcnt` / `tzcnt` capability modeling and define zero-input semantics
2. Thread AArch64 generic `bit_popcount` through the portable intrinsic-lowering path
3. Land concrete `matrix_*` lowering or keep them fenced behind a separate feature gate

### Phase 2: Separate Pass Keys

1. Split `"vectorization"` into `"auto_vectorize"` + `"crypto_idiom"` + `"bit_idiom"`
2. Each individually enabled/disabled via `--disable-pass=crypto_idiom` etc.

### Phase 3: Algorithm Table Expansion

1. Add SHA-512, SM3, SM4 rules (require new stdlib symbols)
2. Add bit-manip symbol rules (rotate, popcount, clz/ctz, bswap, bitrev)
3. Add ChaCha20 quarter-round as a vectorizable idiom (hybrid: crypto + SIMD)

### Phase 4: Cost Model Refinement

1. Replace placeholder latency values with per-µarch tables (Intel ICL/ADL, ARM Cortex-A78/X3, SiFive P870)
2. Add throughput (reciprocal) alongside latency for pipelining decisions
3. Add code-size cost for crypto (relevant for embedded: AES-NI = 4B vs. S-box table = 1KB)

---

## References

- `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` — rule table
- `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` — MIR rewrite engine
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl` — SIMD auto-vectorization
- `src/compiler/60.mir_opt/mir_opt/mod.spl` — TargetOptContext, pass ordering
- `src/compiler/70.backend/feature_caps.spl` — TargetIdiom, X86Caps, Aarch64Caps, Rv64Caps
- `src/compiler/70.backend/backend/native/encode_x86_64_crypto.spl` — x86 byte encoding
- `src/compiler/70.backend/backend/native/encode_rvv_zvk.spl` — RISC-V Zvk encoding
