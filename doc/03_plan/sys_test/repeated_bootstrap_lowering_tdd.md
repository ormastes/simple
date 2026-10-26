# Repeated bootstrap lowering: SPipe TDD plan

Date: 2026-10-09. Scope: the enum repair candidates documented in
`doc/09_report/repeated_bugs.md`, plus their memory/correctness review.

## Requirements and executable evidence

| Requirement | Expected behavior | Executable spec |
|---|---|---|
| REQ-001 | Imported qualified enum fields retain consumer-owned enum identity rather than foreign symbol IDs or aggregate ownership | `test/01_unit/compiler/mir/nested_enum_owner_rebind_spec.spl` |
| REQ-002 | A direct call recovers its declared enum return without guessing enum identity for arrays, scalars, or records | `test/01_unit/compiler/mir/call_return_recovery_spec.spl` |
| REQ-003 | Bare variants resolve against their actual subject; unrelated enum names do not capture valid bindings | `test/01_unit/compiler/mir/enum_subject_match_lowering_spec.spl` |
| REQ-004 | Membership handles ambiguous owners and negative discriminants, preserving ownerless enums and intrinsic optional/result behavior | `test/01_unit/compiler/mir/enum_subject_variant_membership_spec.spl` and match-lowering spec |

Native fixtures under `test/fixtures/compiler/nested_enum_field_provenance`,
`test/fixtures/compiler/enum_scrutinee_owner`, and
`test/01_unit/compiler/mir/fixtures/imported_unwrap_recovery` provide separate
compile/link/run oracles. Rejecting an intentionally invalid fixture is a
positive negative-test result only when the expected diagnostic is observed.

## Bounded red / green / regression sequence

1. Pin the baseline, candidate tree, runtime, backend, and test inventory.
2. Prove the test runner executes assertions using retained trustworthy evidence
   or one failing-assertion control. Parsing failure before assertions means
   zero tests executed, not a reproduction of the target bug.
3. Run each target reproducer against the unchanged baseline. Record the exact
   expected failure; unrelated parse/import/tool failures are infrastructure
   blockers. Existing patches awaiting this step are not completed TDD.
4. Run the same reproducer against the candidate. The implementation must pass
   without changing the expected behavior or suppressing the compiler verifier.
5. Run nearby positive and negative cases once. Include field/call ownership,
   same-spelling variants, scalar/record bindings, optional None/Some, payloads,
   generic/ownerless boundaries, and invalid qualified variants.
6. Run native fixtures separately for LLVM and Cranelift with exact producer
   identities, valid runtime bindings, and no generated unresolved stubs.
7. Record runtime/phase capability skips explicitly. A Phase 1 pass does not
   imply Phase 2/3 native success; unsupported host/backend capabilities may
   be skipped, but crashes and unexpected errors remain failures.

## Memory, performance, and cache invariants

- Validate nominal declaration kind before using an enum registry entry.
- Do not retain foreign symbol IDs or pointers owned by a transient arena.
- New ownership indexes need invalidation on table replacement/publication and
  appropriate retained roots; duplicate lookup candidates must fail closed.
- Preserve source/runtime/backend cache identity. Never relabel an old cache
  or assume reuse from directory existence.
- Measure time and peak memory for performance changes. Semantic-equivalence
  tests normally pass on both baseline and candidate; only an observed cost
  regression test or benchmark establishes performance red/green.

## Current evidence

The identity and pattern patches passed independent Astra source review and
compose against release `4f3788f715d73ff551fe3030e219d5e529ca942b` with clean
diff hygiene. Their original baselines were `fcf72be`.

Executable spec, native fixture, and memory/performance results are **UNRUN**
until the runtime-specific evidence is attached. Structural review is not a
test run. Generated manuals must be refreshed by `simple spipe-docgen` and
report zero stubs before their generation is marked verified.

Each repair uses at most three bounded verify/fix cycles. Preserve successful
results; repeat them only after a relevant source change or new concern.
