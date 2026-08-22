# PerfFacts Def/Use Variant Coverage Is Incomplete

## Status

Partially fixed. Shared def/use facts remain usable only when `def_use_complete` is true.

## Evidence

`perf_instruction_access` now explicitly covers conventional scalar operations plus
ownership transfer, async, SIMD/warp, GPU, VHDL, probes, inline assembly, pipeline
operators, nested place indices, and other specialized MIR variants. Inline-assembly
constant outputs fail closed. `ResultMatchSemantic`, text-encoded `GpuLaunch` arguments,
and the hidden `VhdlProcess` body edge remain deliberately uncovered until their access
or CFG contracts are admitted. References to locals absent from `func.locals` are also
counted and make the result incomplete.

This fail-closed behavior is intentional: an unmodeled operand must not be treated as
unused. It prevents current DCE, vectorization, or escape work from claiming complete
use information over specialized MIR.

## Required fix

1. Give every new opcode an explicit def/use case enforced by a registry self-check.
2. Replace text-encoded GPU launch arguments and model the VHDL process body as a CFG edge.
3. Admit the verification-only result-match metadata contract.
4. Add generated-registry and malformed-local fixtures for every opcode family.
5. Rewire remaining compiler consumers to consume only complete shared facts.

The vectorizer loop dependency path now consumes shared facts and rejects
`analysis_complete=false`. Typed-storage production and storage access summaries use
the same complete-facts gate and shared use counts. Shared block liveness derives from
the same visitor and is unavailable when coverage is partial. The dormant DCE
implementation consumes those facts, returns the original function on incompleteness,
and no longer carries private CFG or per-definition later-use scans. Other private
consumers remain.

## Unblock condition

Opcode-family coverage tests demonstrate zero uncovered instructions across the full MIR
fixture corpus, and consumers reject injected unknown or undeclared-local cases.
