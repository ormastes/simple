# LLVM Backend RISC-V 32-bit Specification

Validates that the LLVM backend correctly generates code for RISC-V 32-bit targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4003 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_riscv32_spec.spl` |
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

Validates that the LLVM backend correctly generates code for RISC-V 32-bit targets.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/llvm_backend_riscv32/result.json` |

## Scenarios

- generates correct riscv32 triple
- contains correct riscv32 layout
- defaults to generic-rv32
- includes standard extensions
- native_int_type is i32
- uses 32-bit target_bits
- uses wfi instruction for halt
- uses i32 size type
