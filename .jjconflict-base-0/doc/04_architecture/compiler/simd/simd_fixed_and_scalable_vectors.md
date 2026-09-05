<!-- codex-design -->
# Architecture: simd_fixed_and_scalable_vectors

## Boundary

This feature formalizes the current two-surface SIMD architecture:

- `FixedVec<T>` is the compatibility-first fixed-width surface.
- `ScalableVec<T>` is the runtime-lane surface for scalable-vector semantics.
- MIR keeps an explicit scalable-vector type.
- native RVV/SVE2 lowering remains outside this slice.

## Public Surface

- `std.simd.fixed.FixedVec<T>`
- `std.simd.scalable.ScalableVec<T>`
- `std.simd.aliases` helper constructors and aliases
- `std.simd` facade exports for the above

`FixedVec<T,N>` syntax remains future design intent only. The executable first
slice keeps the current runtime-`lanes` representation.

## Conversion Contract

- Fixed to scalable: `ScalableVec.from_fixed()` is lossless and unconditional.
- Scalable to fixed: `try_to_fixed(n)` is explicit and runtime-checked.
- No implicit narrowing is allowed.

## Compiler and Backend Contract

- MIR continues to use `MirTypeKind.ScalableVec`.
- The native adapter must expose a stable, testable guard for scalable-vector
  codegen decisions.
- If the selected target lacks scalable-vector capability, the adapter reports
  that explicitly.
- If a scalable-capable RVV path is ever selected before real lowering exists,
  the stable deferred marker remains `riscv_v_native_lowering_deferred`.

## Non-Goals

- No parser migration to const-generic `FixedVec<T,N>`.
- No real RVV native lowering in this slice.
- No SVE2 parity work in this slice.
