# LLVM Backend AArch64 Specification

Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4002 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_aarch64_spec.spl` |
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

Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/llvm_backend_aarch64/result.json` |

## Scenarios

- generates correct aarch64 triple
- contains correct aarch64 layout
- emits datalayout in module header
- defaults to cortex-a53
- includes neon feature
- includes fp-armv8 feature
- native_int_type is i64
- uses 64-bit target_bits
- uses wfi instruction for halt
- uses i64 size type
