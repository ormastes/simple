# Feature Requirement Options: portable_simd_fp_modules

**Date:** 2026-05-01
**Decision required:** choose one option.

## Option A: Scalar FP Only

**Scope**

- Add `f32`/`f64` capability modeling only.
- Add `riscv_fd` and scalar fallback lowering registry entries.
- Defer portable vectors and AVX-specific routing.

**Pros**

- Lowest implementation risk.
- Aligns with existing RISC-V `F`/`D` seams immediately.
- Keeps the compiler surface change small.

**Cons**

- Does not deliver the portable SIMD half of the requested plan.
- Leaves current MIR vector scaffolding unintegrated.
- Delays x86 AVX path selection.

**Effort**

- **Small-Medium**

## Option B: Portable Scalar FP + Fixed-Width SIMD Modules

**Scope**

- Add separate feature families for `scalar_fp`, `vector_simd`, and `target_lowering`.
- Keep the public surface architecture-neutral.
- Ship fixed-width portable vectors in phase 1 with `x86_avx`, `riscv_fd`, and scalar fallback module selection.
- Treat RVV-native scalable vectors as phase 2.

**Pros**

- Matches the supplied plan directly.
- Preserves modular add/remove boundaries.
- Supports RISC-V scalar FP even when `V` is absent.
- Keeps AVX as a backend implementation, not the public API.

**Cons**

- More design surface than scalar-FP-only.
- Requires explicit documentation that RVV-native scalable vectors are deferred.
- Still stops short of full end-to-end backend lowering for every vector op.

**Effort**

- **Medium**

## Option C: Hardware-Specific ISA Surfaces

**Scope**

- Expose AVX and RISC-V vector features directly as separate language-facing APIs.
- Keep per-ISA lowering and diagnostics explicit at the surface level.

**Pros**

- Direct mapping to hardware instructions.
- Minimal abstraction mismatch for ISA-specific users.

**Cons**

- Breaks portability.
- Conflicts with the existing MIR/type direction.
- Harder to keep removable by feature family.

**Effort**

- **Medium-Large**

## Selected Option

Option B, based on the supplied plan.
