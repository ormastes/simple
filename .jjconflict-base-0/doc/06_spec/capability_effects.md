# Capability-Based Effects Specification

Capability-based effect system that prevents LLMs from silently adding I/O or stateful behavior to pure code. Explicit effect markers make side effects visible and checked at compile time.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #880-884 |
| Status | Planned |
| Source | `test/specs/capability_effects_spec.spl` |
| Updated | 2026-03-30 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 0 |
| Slow scenarios | 0 |
| Skipped scenarios | 14 |
| Pending scenarios | 0 |

**Keywords:** effects, capabilities, purity, safety, LLM-safety
**Last Updated:** 2026-01-09
**Topics:** effects, type-system, safety
**Symbols:** Effect, Capability, Pure, IO, Net, FS, EffectChecker
**Module:** simple_compiler::effects
**Migrated From:** doc/06_spec/capability_effects.md

## Overview

Capability-based effect system that prevents LLMs from silently adding I/O or stateful behavior to pure code. Explicit effect markers make side effects visible and checked at compile time.

## Design Goals

1. **LLM Safety:** Prevent accidental side effects in AI-generated code
2. **Explicit Effects:** All effects visible in signatures and modules
3. **Compile-Time Checking:** Effect violations caught at compile time
4. **Fine-Grained Control:** Granular capability requirements

## Related Specifications

- **Type System** - Effect type annotations
- **Module System** - Capability requirements
- **Functions** - Effect propagation and checking

## Scenarios

- [skip] features_1
- [skip] features_capability_inheritance
- [skip] features_effect_annotations
- [skip] features_effect_inference
- [skip] features_pure_by_default
- [skip] features_effect_propagation
- [skip] features_capability_requirements
- [skip] features_generic_effect_constraints
- [skip] features_error_messages
- [skip] features_effect_mismatch
- [skip] features_11
- [skip] features_stdlib_effects
- [skip] examples_pure_module
- [skip] examples_io_boundaries
