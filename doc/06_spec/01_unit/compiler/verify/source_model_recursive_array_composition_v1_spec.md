# Source default and mutual recursive-array composition

Status: AUTHORED UNRUN. Source-authored manual; compiler/tests/Lean/doc generation have not run.

Executable: `test/01_unit/compiler/verify/source_model_recursive_array_composition_v1_spec.spl`. These cases use real parse→HIR→MIR/source-model APIs and both retained Lean backends. No injected semantic type, fabricated default tag or copied compiler algorithm supplies the oracle.

1. should preserve a real field default through HIR codec and materialize its declared recursive array
2. should use explicit array and scalar fields instead of evaluating their defaults again
3. should reject a materialized fixed-array default with the wrong declared length
4. should lower parsed mutually recursive struct and enum declarations with exact array owner
5. should preserve ordinary uncontextualized empty-array inference

The first scenario inspects original and actual codec-roundtripped HirField.has_default/type/default expression, then proves the canonical MIR Array(Node,0) local is produced once and consumed by the actual Node aggregate. It separately checks the ordinary i64 default. The explicit override control proves defaults are not materialized again. Parsed mutual declaration metadata checks both directions of the actual nominal graph before exporter assertions. Final generated Lean elaboration/native refinement remains UNRUN.
