# LLVM Backend ARM 32-bit Specification

Validates that the LLVM backend correctly generates code for ARM 32-bit (ARMv7) targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4004 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_arm32_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Validates that the LLVM backend correctly generates code for ARM 32-bit (ARMv7) targets.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/llvm_backend_arm32/result.json` |

## Scenarios

- generates correct armv7 triple
- includes gnueabihf env on linux
- contains correct arm32 layout
- defaults to cortex-a7
- includes neon feature
- includes vfp4 feature
- native_int_type is i32
- uses 32-bit target_bits
- uses wfi instruction for halt
- uses i32 size type
