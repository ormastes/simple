# Lean declaration verification plan

Run once on a qualified self-hosted runtime after composition:

- `test/03_system/compiler/lean_type_declarations_spec.spl`: 19 real plugin/API scenarios covering exact output, ordering, nominal function signatures, metadata and refusal paths.
- `test/03_system/compiler/lean_type_declarations_owner_spec.spl`: 4 compiler-owner public-module scenarios, including the actual repaired translator import path.
- Type-check generated Lean modules for ordinary/empty declarations, cross-type payloads, root-qualified primitive/composite types, exact metadata and the nominal identity function. A Simple assertion on emitted text is not a Lean elaboration PASS.
- Run required compiler/lib/MCP/LSP checks and smoke gates under the parent plan. Preserve any known pre-existing failures with exact evidence; never relabel them green.

Manual source: `doc/06_spec/03_system/compiler/lean_type_declarations_spec.md`. It is hand-authored from executable scenarios, not runner-generated proof of execution. Current status: all executable, coverage, Lean elaboration and performance gates UNRUN. Independent source review is pending. Maximum three correction/review cycles; do not rerun green criteria.

Revision 2 adds the C2-DECL-01 counterexamples: each of ctorIdx, ctorElimType and ctorElim paired with Other in a two-variant enum. Both owners assert named rejection through full/generated module APIs and retained builder contents. Existing green source findings are not replayed. All runtime scenarios remain UNRUN.
