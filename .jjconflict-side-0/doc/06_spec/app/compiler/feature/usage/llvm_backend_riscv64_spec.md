# LLVM Backend RISC-V 64-bit Specification

Validates that the LLVM backend correctly generates code for RISC-V 64-bit targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4005 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_riscv64_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Validates that the LLVM backend correctly generates code for RISC-V 64-bit targets.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/llvm_backend_riscv64/result.json` |

## Scenarios

- generates correct riscv64 triple
- contains correct riscv64 layout
- defaults to generic-rv64
- includes standard extensions
- native_int_type is i64
- uses 64-bit target_bits
- uses wfi instruction for halt
- uses i64 size type
