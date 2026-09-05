# Feature Requirements: SIMD Auto-Application

Date: 2026-05-03
Status: Selected from prior plan

## Functional requirements

- REQ-001: The MIR optimizer shall recognize elementwise scalar loops that can be safely rewritten into vector-loop scaffolding without source changes.
- REQ-002: Phase-1 elementwise support shall include `add`, `sub`, `mul`, and `xor`.
- REQ-003: The optimizer shall keep `fast_math` gating for FP reductions and reassociation-sensitive transforms only.
- REQ-004: The compiler shall define canonical MIR intrinsic names for portable bit-idiom families and matrix-kernel families.
- REQ-005: Backend capability routing shall classify support across fixed-width SIMD, scalable SIMD, bitmanip, crypto, and matrix classes.
- REQ-006: The MIR optimizer shall recognize canonical matrix-kernel inner loops at least to the level of recipe/logging support.
- REQ-007: Existing crypto/compression code shall remain eligible for future compiler-first adoption without requiring public API redesign.

## Out of scope for this phase

- full tile-engine backend enablement
- arbitrary matrix expression lowering
- mandatory new public stdlib SIMD or matrix APIs
