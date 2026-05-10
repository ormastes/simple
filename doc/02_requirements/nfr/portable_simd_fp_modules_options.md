# NFR Options: portable_simd_fp_modules

**Date:** 2026-05-01
**Decision required:** choose one option.

## NFR A: Minimal Correctness Only

**Targets**

- Capability and lowering selection remain deterministic for covered presets.
- Unsupported combinations report explicit diagnostics.

**Pros**

- Lowest verification cost.
- Good fit for an initial registry-only milestone.

**Cons**

- Too weak for future hot-path numeric work.
- Does not set performance or modularity guardrails.

**Effort**

- **Small**

## NFR B: Modularity And Diagnostic Focus

**Targets**

- Each feature family can be enabled or disabled without changing unrelated target behavior.
- Capability derivation for `scalar_fp`, `vector_simd`, and target-specific lowering remains deterministic from preset input plus runtime probe requirements.
- Unsupported vector requests produce explicit diagnostics rather than silent fallback.
- The module-selection layer must keep a scalar fallback path available whenever target lowering is enabled.

**Pros**

- Best fit for the current phase-1 capability-layer milestone.
- Protects later backend work from hidden coupling.
- Easy to verify with compiled tests.

**Cons**

- Does not yet impose numeric performance targets.
- Still requires follow-up perf evidence once lowering is integrated.

**Effort**

- **Small-Medium**

## NFR C: Performance-Qualified Phase 1

**Targets**

- Add startup, latency, and RSS budgets for numeric capability selection and later lowering paths.
- Add representative vector and scalar microbenchmarks now.

**Pros**

- Strongest discipline for future backend performance.

**Cons**

- Premature for a registry-first milestone.
- Adds verification overhead before end-to-end lowering exists.

**Effort**

- **Medium-Large**

## Selected Option

NFR B, based on the supplied plan.
