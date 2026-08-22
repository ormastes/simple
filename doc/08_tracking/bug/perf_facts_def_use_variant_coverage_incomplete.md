# PerfFacts Def/Use Variant Coverage Is Incomplete

## Status

Open. Shared def/use facts are usable only when `def_use_complete` is true.

## Evidence

`perf_instruction_access` covers conventional scalar arithmetic, memory, aggregate,
cast, call, intrinsic, debug, and terminator operands. Ownership-transfer, async,
SIMD/GPU, VHDL, probes, inline assembly, pipeline operators, and other specialized MIR
variants currently return uncovered. References to locals absent from `func.locals` are
also counted and make the result incomplete.

This fail-closed behavior is intentional: an unmodeled operand must not be treated as
unused. It prevents current DCE, vectorization, or escape work from claiming complete
use information over specialized MIR.

## Required fix

1. Add exhaustive def/use extraction beside the canonical MIR opcode owner.
2. Give every new opcode an explicit def/use case enforced by a registry self-check.
3. Cover normal instructions, terminators, inline-assembly operands, projections,
   ownership transfers, suspension, device operations, and verification metadata.
4. Add declared-local validation and fixtures for every opcode family.
5. Rewire vectorization and storage analyses to consume only complete shared facts.

## Unblock condition

Opcode-family coverage tests demonstrate zero uncovered instructions across the full MIR
fixture corpus, and consumers reject injected unknown or undeclared-local cases.
