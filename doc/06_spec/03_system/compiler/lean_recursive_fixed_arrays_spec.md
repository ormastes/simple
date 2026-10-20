# Recursive fixed-array API scenarios

Status: AUTHORED UNRUN. Source-authored manual; doc generation, compiler, Simple test and Lean execution have not run.

Executable: `test/03_system/compiler/lean_recursive_fixed_arrays_spec.spl`. Canonical MIR/frontend APIs and real full/generated module exporters are used. Every positive unwraps the real Result; negatives assert actual errors and preserved borrowed state/builders. Output assertions do not prove Lean elaboration or native layout.

1. should export a self-recursive finite enum payload through all four module APIs
2. should construct a zero-length recursive struct field without an element inhabitant
3. should preserve ordered genuine nominal operands in singleton and multi-element arrays
4. should make mutual recursive representation independent of declaration insertion order
5. should use one exact carrier for unrelated fields parameters returns and locals
6. should select both nested recursive array shapes through positive wrappers
7. should retain ordinary Vector mapping for scalar and unselected nominal array lengths
8. should reject malformed nominal identity even under an empty array atomically
9. should reject negative recursive array lengths before builder mutation
10. should reject aggregate element count mismatch without changing the borrowed module
11. should reject repeated Move operands in a selected carrier
12. should admit exact depth and node boundaries through the actual planner
13. should admit exact retained-key bytes and reject one byte less
14. should charge unique policy entries and reuse repeated exact shapes
15. should enforce work admission before final plan growth
16. should reject invalid downward overrides and preserve the two-argument API
17. should charge repeated exact-policy lookups instead of providing an unbounded cache bypass

The optional planner limits are downward-only and validated before planning. Exact lower-budget boundaries make resource admission testable through the same production entrypoint; no private policy is manufactured. Constructor/default coverage and whole-module composition are separate.
