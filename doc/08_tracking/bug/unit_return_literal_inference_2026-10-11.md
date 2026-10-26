# Explicit unit returns misclassified as unknown value returns

Status: narrow source repair applied locally; executable verification UNRUN.

The native diagnostic for `expr_dispatch.spl` rejects
`emit_pending_finally_for_transfer` as an unannotated value-returning method.
Its early `return ()` is valid unit syntax. Both return scanners preserve the
value, but `infer_simple_type_name_ast` had no empty `TupleLit` case, making the
return scan ambiguous. Adding a caller annotation would hide the inference bug.

The repair recognizes only empty tuples as `unit`, explicitly maps that name to
`HirTypeKind.Unit`, and maps Unit back to its name for typed parameter returns.
Unit remains excluded from the arithmetic scalar predicate. Nonempty tuple and
unknown-call inference is unchanged; mixed unit/value returns remain ambiguous.

Seven real compiler consumer groups are in
`test/01_unit/compiler/hir/unit_return_inference_spec.spl`. They cover both AST
return representations, bare returns, parsed callable signatures, type-name
round trips, both mixed-return orders, nonempty tuples, unit arithmetic and an
unknown call. The unary-negation path now rejects only the newly recognized
`unit` operand name, retaining its original result for every other operand.
Additional actual-owner controls cover `-()`, parsed typed Unit negation, four
scalar literal names, and eight typed scalar return/callable signatures. They
contain no copied inference implementation. All seven cases are UNRUN.

The static-only driver tests remain separate and UNRUN. Their emitted-object
symbol/initializer binding and missing-specialization-with-surviving-static
coverage remain pending limitations; no object tooling or acceptance is implied.

Reviewed packet: `build/native_probe/unit-return-inference-20261011/SEALED.json`.
The production test packaging addendum removes the private app fixture import.
The active six-module native run intentionally retains its earlier frozen
source and does not verify this repair. Native behavior and performance/memory
admission require a coherent qualified producer/source pair; no release PASS or
speed improvement is claimed from this source change.
