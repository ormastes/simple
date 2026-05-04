# Security Extension Optimization — Multi-Arch Implementation Plan

## Architecture Decision: Discriminated Enum, Not Trait Polymorphism

Simple's runtime does not support dynamic dispatch on trait objects as function parameters.
The plan uses a discriminated `TargetCapsKind` enum:

```
enum TargetCapsKind:
    X86(X86Caps)
    Aarch64(Aarch64Caps)
    Rv64(Rv64Caps)
    None
```

All multi-arch dispatch via `match caps_kind:` blocks calling existing per-arch free functions.

---

## Implementation Sequencing

```
Phase 1 (Multi-Arch MIR Rewrite)
  |
  v
Phase 2 (Separate Pass Keys)     -- can overlap with Phase 1 tail
  |
  v
Phase 3A (Rules + Idioms)        -- depends on Phase 1
  |
  v
Phase 3B (Backend Encoders)      -- deferrable indefinitely
  |
  v
Phase 4 (Cost Model)             -- depends on Phase 1 + 3A
```

Phases 2 and 3A can proceed in parallel once Phase 1 lands.

---

## Phase 1: Multi-Arch MIR Rewrite

**Goal:** Lift the pattern-idiom pass from x86-only to architecture-generic.

### Files Modified

| File | Change |
|------|--------|
| `src/compiler/70.backend/feature_caps.spl` | Add `enum TargetCapsKind` + `caps_kind_supports()` + `caps_kind_target_name()` dispatchers |
| `src/compiler/60.mir_opt/mir_opt/mod.spl` | Add `caps_kind: TargetCapsKind` to `TargetOptContext`; dispatch to generic pass |
| `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` | Add `rewrite_block_generic()` + `run_pattern_idiom_pass_generic()` |
| `src/app/build/build_cli.spl` | Detect target arch → construct appropriate `TargetCapsKind` in `build_driver_flags_to_target_opt_ctx` |
| `src/compiler/60.mir_opt/mir_opt_integration.spl` | Add `optimize_mir_module_with_caps_kind()` entry point |

### Key Design Decisions

- Keep existing `X86Caps`-typed entry points for backward compatibility
- Default `target_opt_context_default()` sets `caps_kind: TargetCapsKind.None`
- When `caps_kind` is `None`, fall back to `x86_caps` field (exact backward compat)

### Risks

- `TargetOptContext` struct change is viral — every constructor site needs the new field
- `BuildDriverFlags` may not carry `CodegenTarget` — plumbing needed through `80.driver/build/types.spl`

### Testing

- New: `test/unit/compiler/mir_opt/cipher/pattern_dispatch_generic_spec.spl`
- Regression: existing x86 pattern_dispatch specs pass unchanged

---

## Phase 2: Separate Pass Keys

**Goal:** Split `"vectorization"` into `"pattern_idiom"` (crypto + bit-manip) and `"auto_vectorize"` (SIMD loops).

### Files Modified

| File | Change |
|------|--------|
| `src/compiler/60.mir_opt/mir_opt/mod.spl` | Add `"pattern_idiom"` to `Speed` and `Aggressive` pipelines; route to `run_pattern_idiom_pass_generic`; remove cipher rewrite from `"vectorization"` branch |

### Key Design Decisions

- `"pattern_idiom"` runs after `"inline_functions"` (call sites expanded) and before `"body_outlining"`
- `"vectorization"` becomes reserved for future auto-vectorization only
- Enables `--disable-pass=pattern_idiom` to suppress crypto rewrites independently

### Risks

- Pass ordering sensitivity: cipher rewrite must see inlined call sites
- Any external code referencing `"vectorization"` for cipher rewrites silently breaks

---

## Phase 3: Algorithm + Bit-Manip Table Expansion

### Phase 3A: Rules + Idiom Names (Cheap)

| File | Change |
|------|--------|
| `src/compiler/50.mir/intrinsics.spl` | Add `BIT_PARITY`, `CRYPTO_SHA512_*` name constants |
| `src/compiler/70.backend/feature_caps.spl` | Add `TargetIdiom` variants: `Parity`, `Sha512Rounds2/Msg1/Msg2`; extend `supports`/`cost` in all three impls; add `has_sha512` to `Aarch64Caps`, `has_zvknhb` to `Rv64Caps` |
| `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` | Add 7 bit-manip rules (`rotate_left/right`, `count_ones`, `leading_zeros`, `trailing_zeros`, `reverse_bits`, `parity`) + SHA-512 rules |
| `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` | Extend `idiom_for_intrinsic()` with new mappings |
| `src/compiler/70.backend/lowering/intrinsic_lowering_{x86,aarch64,riscv}.spl` | Add lowering cases (some return `"unimplemented"`) |

### New Stdlib Symbol → Intrinsic Rules

| Symbol | Intrinsic | Requires |
|--------|-----------|----------|
| `std.common.bitwise_utils.rotate_left` | `bit_rotate_left` | `bitmanip` |
| `std.common.bitwise_utils.rotate_right` | `bit_rotate_right` | `bitmanip` |
| `std.common.bitwise_utils.count_ones` | `bit_popcount` | `popcnt` |
| `std.common.bitwise_utils.leading_zeros` | `bit_clz` | `bitmanip` |
| `std.common.bitwise_utils.trailing_zeros` | `bit_ctz` | `bitmanip` |
| `std.common.bitwise_utils.reverse_bits` | `bit_bitreverse` | `bitmanip` |
| `std.common.bitwise_utils.parity` | `bit_parity` | `popcnt` |
| `std.common.sha512.sha512_round` | `crypto_sha512_rnds2` | `sha512` |
| `std.common.sha512.sha512_msg_schedule_1` | `crypto_sha512_msg1` | `sha512` |
| `std.common.sha512.sha512_msg_schedule_2` | `crypto_sha512_msg2` | `sha512` |

### Phase 3B: Backend Encoders (Deferrable)

- AArch64 SHA-512 encoder (`emit_sha512h`, `emit_sha512h2`, etc.)
- RISC-V Zvknhb SHA-512 encoder (same Zvk opcodes with SEW=64)
- ROL/ROR encoders for all three architectures
- Until landed, rules with `"unimplemented"` lowering leave the original Call in place (correct fallback)

### Risks

- Adding `TargetIdiom` variants requires exhaustive `match` updates in ALL THREE `impl TargetCaps` blocks + all lowering files
- Struct field additions to `Aarch64Caps`/`Rv64Caps` break every constructor site

---

## Phase 4: Cost Model Refinement

**Goal:** Gate rewrite on `hw_cost < sw_cost`, not just `supports`.

### Files Modified

| File | Change |
|------|--------|
| `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` | Add cost gate in `rewrite_block_generic`: `if caps_kind_cost(kind, idiom) >= rule.software_cost: skip` |
| `src/compiler/70.backend/feature_caps.spl` | Add `caps_kind_cost()` dispatcher; refine per-µarch latency values |
| `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` | Add `software_cost: i64` field to `Rule` |
| `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` | Set `software_cost` for each rule |
| `src/compiler/60.mir_opt/mir_opt/pattern/cost_model.spl` | Add `should_rewrite(hw_cost, sw_cost, threshold)` |

### Software Cost Estimates

| Operation | Software Cost (cycles) | Hardware Cost (cycles) |
|-----------|----------------------|----------------------|
| AES round | 100-200 | 4 (AES-NI/AESE/Zvkned) |
| SHA-256 round pair | 50-80 | 6 (SHA-NI/SHA256H/Zvknh) |
| CRC32 byte | 20-40 | 2 (SSE4.2/CRC32) |
| CLMUL | 40-80 | 7-8 (PCLMUL/PMULL/Zvkg) |
| Popcount | 10-15 | 1-2 (POPCNT/CNT/cpop) |
| Rotate | 3-5 | 1 (ROL/ROR) |

### Risks

- Test breakage guaranteed — existing tests assume "supports == rewrites"
- Default `software_cost = 0` would prevent all rewrites; default to large value (1000)

---

## Critical Files (Touched Across Multiple Phases)

1. `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` — all 4 phases
2. `src/compiler/60.mir_opt/mir_opt/mod.spl` — Phases 1, 2
3. `src/compiler/70.backend/feature_caps.spl` — Phases 1, 3, 4
4. `src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl` — Phases 3, 4
5. `src/app/build/build_cli.spl` — Phase 1

## Missing Algorithm Coverage Status

| Algorithm | x86 | ARM | RISC-V | Rules | Backend Encoder |
|-----------|-----|-----|--------|-------|-----------------|
| AES | AES-NI | AESE/AESD | Zvkned | Done | Done |
| SHA-256 | SHA-NI | SHA256H | Zvknh | Done | Done |
| CRC32 | SSE4.2 | CRC32 | — | Done | Done |
| CLMUL | PCLMULQDQ | PMULL | Zvkg | Done | Done |
| SHA-512 | — | SHA512H | Zvknhb | Phase 3A | Phase 3B |
| SM3 | — | — | Zvksh | Future | Future |
| SM4 | — | — | Zksed | Future | Future |
| ChaCha20 | (AVX2 vec) | (NEON vec) | — | Future | N/A |
| Bit-manip | (POPCNT etc) | (NEON etc) | (Zbb/Zbkb) | Phase 3A | Phase 3B |
