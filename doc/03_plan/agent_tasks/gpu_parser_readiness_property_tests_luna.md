# GPU Parser Readiness Property-Test Lane (Luna)

## Ownership

- Lane owner: Luna
- Merge owner: root Codex
- Final reviewer: root normal/highest-capability verification pass
- Scope: executable readiness properties and their manual/plan evidence only
- Forbidden: grammar edits, GPU kernels, production parser implementation,
  replacing missing owners with test-only implementations

## Frozen interfaces and IDs

The lane uses the existing `ParseDialect`, `ParseRequest`, `ParseResult`,
`ParseLexProgram`, `ParallelLexPlan`, and `IncrementalParsePlan` surfaces.
Property IDs are frozen as:

`GPU-PREP-V001` per-dialect grammar manifests and digests; `GPU-PREP-V002` progress/lookahead;
`GPU-PREP-V003` bounded arenas/count-emit; `GPU-PREP-V004` region partition;
`GPU-PREP-V005` fallback/recovery/cancellation/generation;
`GPU-PREP-V006` incremental equivalence; `GPU-PREP-V007` generated-consumer
equivalence.

V001/V007 use dialect-scoped parity, not one digest across unrelated
languages. The Simple grammar digest binds compiler/interpreter, native+Wasm
Tree-sitter projection, and `.shs`; `.shs` is full Simple plus `std.shell`
imports and is not `SoshDialect`. SDN binds `SdnDialect`, while
`src/os/apps/shell/**` binds `SoshDialect`. Public API and diagnostics must
remain equivalent within each dialect set.

Manual step names are `Build the canonical flat lexical manifest`, `Run the
scalar oracle on an empty source and a representative source`, `Submit a
source larger than its exact source-byte capacity`, `Require a region-partition
oracle proving ordered disjoint coverage`, `Run the CPU oracle and the
requested accelerated mode`, `Build the clean request used as the CPU
reference`, and `Parse a valid source through the canonical scalar dialect`.

## Deliverables

- executable RED spec:
  `test/03_system/app/compiler/feature/gpu_parser_readiness_property_spec.spl`
- test plan and property matrix:
  `doc/03_plan/sys_test/gpu_parser_readiness_property.md`
- generated/manual mirror:
  `doc/06_spec/03_system/app/compiler/feature/gpu_parser_readiness_property_spec.md`

Every unowned production boundary uses an explicit `MissingEvidence:<ID>:<owner>`
failure. A future owner may remove that marker only after independent receipt
evidence exists. CPU fallback is retained as the oracle and is never counted
as GPU execution.

## Dependencies and handoff

Formal/static verification should align to V001–V007. The parser-unification
agent owns canonical grammar/consumer wiring; the GPU-preparation agent owns
bounded chunk/region/count-emission contracts. Root merges this lane after
those interfaces are frozen, then reruns the spec once per acceptance cycle.

## Evidence status

The source compiled and executed with the repository test runner. The result
was 12 scenarios / 12 explicit MissingEvidence failures, which is expected
RED evidence for the current implementation state.
