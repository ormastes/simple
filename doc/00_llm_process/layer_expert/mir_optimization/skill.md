# MIR Optimization Layer Expert

## Ownership

Own `src/compiler/60.mir_opt/**`, including pass descriptors, effective pipelines,
shared `PerfFacts`, transform legality/profitability, structured remarks, and
analysis invalidation. Coordinate typed collection diagnostics with
`src/compiler/35.semantics/lint/**`; do not move typed semantic ownership into MIR.

## Required invariants

- A registered pass has one stable name, aliases, scope, provider, cost class,
  `PassStatus`, and `PassExpectation`.
- Only `Active` transforms dispatch. Requested inventory never implies activation.
- An active transform has an executable positive sentinel and changed-pass verifier.
- CFG order is not dominance. Block ID order is not CFG order.
- Loop movement requires a real preheader and zero-trip/speculation proof.
- Bounds/range facts are dominance-scoped and invalidated by relevant writes.
- Unknown effects, aliasing, calls, pointers, or escape flows fail closed.
- `PerfFacts` owns common graph and memory facts; consumers declare preservation.
- General fusion requires domain, dependence, alias, effect/order, exit, numeric,
  and profitability proofs.

## Review gates

Check zero/one/many trips, irreducible CFG, alias traps, exceptional flow, overflow,
floating-point mode, unsafe pointers, ownership/COW, destruction order, backend
matrix, idempotence, IR verification, and unoptimized/optimized differential output.

Do not accept a performance claim without compile-time/runtime/allocation evidence
from an admitted pure-Simple binary.
