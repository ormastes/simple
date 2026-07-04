<!-- codex-research -->
# Domain Research: portable_simd_fp_modules

## Primary Sources

- Intel AVX2 intrinsics guide:
  - https://www.intel.com/content/www/us/en/docs/cpp-compiler/developer-guide-reference/2021-9/intrinsics-for-avx2.html
- RISC-V Unprivileged ISA index:
  - https://docs.riscv.org/reference/isa/unpriv/unpriv-index.html
- RISC-V V extension:
  - https://docs.riscv.org/reference/isa/unpriv/v-st-ext.html
- LLVM LangRef vector types:
  - https://releases.llvm.org/10.0.0/docs/LangRef.html

## Findings

- Intel AVX and AVX2 are fixed-width vector models centered on 256-bit YMM registers. AVX2 extends AVX with 256-bit integer operations while reusing the same packed floating-point programming model and VEX encoding family.
- The current RISC-V ratified unprivileged ISA separates scalar floating point into `F` (single precision) and `D` (double precision), both listed as independent standard extensions in Volume I.
- The ratified `V` extension is not fixed-width. It defines implementation parameters such as `VLEN` and `ELEN`, exposes `vl`, `vtype`, and `vlenb`, and supports portable binaries by varying active vector length at runtime rather than committing to one fixed register width.
- The `V` extension’s floating-point instructions require corresponding scalar FP support. The spec states that vector floating-point instructions require the base scalar floating-point extensions for the supported element widths, and the full `V` extension depends on `F` and `D` for 32-bit and 64-bit FP vector operations.
- LLVM IR distinguishes fixed-length vectors from scalable vectors:
  - fixed: `<N x ty>`
  - scalable: `<vscale x N x ty>`
  This matches the architectural split between AVX-style fixed-width SIMD and RVV-style scalable vectors.

## Design Implications

- A portable user-facing vector API can stay fixed-width in phase 1 and still lower efficiently to AVX/AVX2.
- Scalar floating point should be a separate feature family from vector SIMD because RISC-V `F`/`D` can be present without `V`.
- RVV-native support should not be forced into the existing fixed-width MIR types. Doing so would either leak hardware-width assumptions or mis-model scalable semantics.
- The correct near-term split is:
  - phase 1: scalar FP + fixed-width portable vectors + scalar fallback + backend-specific fixed-width lowerings,
  - phase 2: scalable-vector MIR and RVV-native lowering when the IR can express `vscale` semantics explicitly.
