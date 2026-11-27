# Impl-generic method semantic return was not published

Actual focused run `45194358128` executed verified Phase 1 producer
`52b6fb7ba8cefa37a8d459e98068758fbfc5842ba6b12777000b4721355cb8cf`, source
`5e436b9e62384ac3c52f98f4a7032e332d7764bf`. Its 14-file real AttributeStore
fixture failed at the unannotated `store.get(3)` match: RTI resolved `b:i64`
instead of the provider's declared `Result<T, text>`. No entry artifact or
suite execution resulted. Evidence remains under
`build/verify/owner-probe-evidence/run-45194358128/actual_attribute_store`.

The bootstrap module predeclaration intentionally leaves `impl<T>` method
symbols untyped until the impl scope binds its parameters. Function lowering
keeps aggregate body returns on the tagged-word ABI, but republished semantic
signatures only for functions declaring their own type parameters. A method
with zero own parameters under a generic impl therefore retained no semantic
signature; RTI could publish its physical i64 return as a declaration.

Repair: `lower_impl` passes its actual lowered binder vector to `lower_function`.
The semantic publication branch includes this bound owner context when an
actual nominal owner is installed. It preserves the existing body ABI, owner
identity, binder order, and method-owned parameters. RTI acceptance guards and
consumer source annotations are unchanged.

The focused HIR regression checks owner-generic Result publication and text
instantiation, wrong-owner lookup rejection, unbound return parameter rejection,
and nongeneric/method-generic controls. It has not been executed by an admitted
compiler. The actual native fixture must be rerun only with a fresh reviewed
producer; cycle 5 is failing evidence, not qualification.
