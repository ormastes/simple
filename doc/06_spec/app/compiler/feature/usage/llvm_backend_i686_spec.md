# LLVM Backend i686 (x86 32-bit) Specification

Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #4001 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/llvm_backend_i686_spec.spl` |
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

Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.
This includes target triple generation, datalayout, native integer types, and CPU defaults.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/llvm_backend_i686/result.json` |

## Scenarios

- generates correct i686 triple
- includes correct OS in triple
- contains 32-bit pointer specification
- emits datalayout in module header
- uses 32-bit target_bits
- native_int_type is i32
- defaults to i686 CPU
- includes sse2 feature
- works for i686
- uses i32 size type for memcpy/memset
