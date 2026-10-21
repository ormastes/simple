# Recursive fixed-array API scenarios

Status: AUTHORED UNRUN. Source-authored manual; doc generation, compiler, Simple test and Lean execution have not run.

Executable: `test/01_unit/compiler/verify/source_model_recursive_fixed_arrays_v1_spec.spl`. Canonical MIR/frontend APIs and real full/generated module exporters are used. Every positive unwraps the real Result; negatives assert actual errors and preserved borrowed state/builders. Output assertions do not prove Lean elaboration or native layout.

1. should export an actual parsed recursive enum array signature
2. should return a producer-validated array payload with the same continuation type
3. should transport the same recursive array through an actual match join
4. should construct an actual source zero-length recursive struct

The optional planner limits are downward-only and validated before planning. Exact lower-budget boundaries make resource admission testable through the same production entrypoint; no private policy is manufactured. Constructor/default coverage and whole-module composition are separate.
