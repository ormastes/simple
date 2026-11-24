# Owner-generic method semantic return: historical evidence and complementary regression

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

At the historical ce231 source, `lower_function` previously published the lowered semantic signature only when
the function had its own generic binders. `get` has none: `T` belongs to its
enclosing implementation. The ce231 repair also fills an untyped, exact-name,
current-module declaration while lowering a method owner. It uses the declared
return and parameters after binding, preserves already typed signatures and
physical ABI, and does not rewrite imported declarations or invent an enum type.

Regression: `test/01_unit/compiler/hir/generic_method_semantic_return_spec.spl`.
It lowers real source, checks the zero-method-binder signature and RTI owner
parameter, substitutes `text`, and checks an ordinary typed function. Under
bootstrap policy it also checks that the physical method ABI remains `i64`.
The ce231 implementation received independent source review. Its later evidence is
recorded below; none of it is qualification of the release implementation.

## Historical ce231 qualification boundary

The unchanged regression executed in paired run 45254088363: the baseline ran
one example with one failure; ce231 ran one example with zero failures. Both
lowered the same two functions. Native Phase1 run 45254614898 produced compiler SHA256
`ed5e03685a3c9233395306f6fcb2c7c5fa9a6ada36fc1158c20e6d3be91fcf73`
and compiled/executed its native Hello successfully. Native fixture replay
45259641764 compiled 14/14 modules without failures and emitted the real
405248-byte ELF object SHA256
`79f19dc06de194085eb0c5ad2cda594f8e8d36654d2364cb18fee0ab9ca26248`.
That replay workflow remains failed because its separate metadata collector was
incomplete; the object evidence is not runtime or workflow qualification.
Canonical Phase2 continuation 45275222826 is bound to immutable source
`ce231b5b898d797c98d44a9b59a4859a7d792a7b`. Its eventual result cannot qualify
this merge head or alter the source identity of that live lineage.

## Release integration and remaining scope

Release already contains `1dadda21490eebb8a5f84ac397b579f380fd038f`, carried by
PR11118. It passes the actual lowered impl binders into `lower_function` and
publishes owner-generic method returns while retaining the physical ABI. The
canonical declaration pass creates fresh local method rows before lowering;
there is no demonstrated imported/typed-row regression requiring the older
ce231 fallback predicate. Static generic-owner methods participate as well.
The release repair's report explicitly states its regression was unexecuted;
its inclusion through a diagnostic inspection PR is not native qualification.

PR11133 now retains only this historical report and the complementary test.
The merge takes the production implementation byte-for-byte from release
`073900245d2d017137ea699676470ac629bc5a51`, including its impl-binder interface
and Option handling. The test adds actual bootstrap entry-closure setup and
restoration, method/ordinary declaration counts, semantic Result/RTI
substitution, and the physical bootstrap i64 assertion. Its assertions are
unchanged from ce231. Execution against the new merged source remains pending;
no earlier passing result is relabeled as a new-head pass.
