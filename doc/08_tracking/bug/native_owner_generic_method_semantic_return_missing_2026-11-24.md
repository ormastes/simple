# Owner-generic method loses declared semantic return — open

Linux canonical rung2 run 45211128098, job 137849962056, source
68bb1b5d22340f9f730d37e584033793a821f0ce fails in `_AstExpr.nodes.spl`
at `match store.get(3)`. The exact producer SHA-256 is
58f5b949aa5011f164ef7965fdaf095104fbd6023c74b3956bf8a0cf1b08885c.
The fatal diagnostic rejects an enum match without complete declaration ownership.

The real `actual_attribute_store.spl` fixture reproduces the three fatal errors
outside the shard path in bounded emit-object runs 45246079549 and 45247677245.
Both owners finish with exit 1; the latter peaks at 2,955,060 KiB under a 6 GiB
cap. These are pre-link diagnostics, with no runtime-pairing qualification.

The latter artifact retains the actual provider HIR. Its owned
`AttributeStoreV1::get` symbol has no `type_`, although the imported signature
retains `Result<T, text>`. The provider's physical bootstrap function return is
`i64`, which becomes the RTI fallback. The owner is present: this is not evidence
for relaxing the declaration-ownership check.

`lower_function` previously published the lowered semantic signature only when
the function had its own generic binders. `get` has none: `T` belongs to its
enclosing implementation. The repair also fills an untyped, exact-name,
current-module declaration while lowering a method owner. It uses the declared
return and parameters after binding, preserves already typed signatures and
physical ABI, and does not rewrite imported declarations or invent an enum type.

Regression: `test/01_unit/compiler/hir/generic_method_semantic_return_spec.spl`.
It lowers real source, checks the zero-method-binder signature and RTI owner
parameter, substitutes `text`, and checks an ordinary typed function. Under
bootstrap policy it also checks that the physical method ABI remains `i64`.
Independent source review passed; execution and a patched native producer remain
pending. This report does not claim that the canonical rung is repaired.
