<!-- codex-research -->
# NFR: portable_simd_fp_modules

## Selected Option

NFR Option B: Modularity And Diagnostic Focus.

## Requirements

- NFR-PSFM-001: Capability derivation from a target preset must be deterministic.
- NFR-PSFM-002: Feature-family enablement must be orthogonal: disabling one family must not change the capability result of unrelated families.
- NFR-PSFM-003: Target-lowering selection must always keep scalar fallback available when `target_lowering` is enabled.
- NFR-PSFM-004: Unsupported vector requests must produce explicit diagnostics.
- NFR-PSFM-005: x86_64 vector-capability decisions that depend on runtime CPU features must be marked as requiring a runtime probe rather than assumed from the generic preset alone.
- NFR-PSFM-006: The phase-1 implementation must not claim RVV-native scalable-vector support while MIR remains fixed-width.
