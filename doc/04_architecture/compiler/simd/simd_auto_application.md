# Architecture: SIMD / Matrix / Bit-ISA Auto-Application

Date: 2026-05-03

## Three-lane model

### Lane A: auto-vectorize

- Works at MIR level.
- Recognizes scalar loop shapes already present in libraries.
- Emits vector-loop scaffolding plus scalar remainder handling.
- Uses target capability helpers to choose preferred lane width.

### Lane B: ISA idiom lowering

- Portable MIR intrinsic names represent scalar bit idioms.
- Backend lowering decides whether an idiom becomes a native instruction or stays scalar.
- This keeps source and MIR portable while still exposing ISA acceleration.

### Lane C: matrix-kernel recognition

- Recognizes inner kernels, not arbitrary source-level matrix syntax.
- Phase 1 targets:
  - dot product
  - outer-product update
  - matvec-like loops
- Phase 1 architecture stops at recipe recognition and future rewrite hooks.

## Shared capability plane

`src/compiler/70.backend/feature_caps.spl` is the shared legality/cost surface.

It now provides:

- fine-grained `TargetIdiom`
- coarse `TargetFeatureClass`
- preferred lane-count helpers derived from target vector width

This is the planning seam between MIR optimization and backend lowering.

## Phase boundaries

- This turn lands compiler-visible infrastructure and recipe recognition.
- Backend encoders for the new bitmanip family remain a follow-up.
- Matrix kernels are architecture-ready but not yet fully lowered.
