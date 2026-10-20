# Trait-typed receiver whose implementor is in another unit lowers to a bare-name extern

`strategy.implementation_identity()` (pure_database.spl, `strategy` bound from
`Option<PureDatabaseBitmapReducerV1>`) reaches codegen as a Call to the bare
name `implementation_identity`, not a virtual/trait dispatch. When no
implementor is in the same unit, Cranelift declares an `Import` of that bare
symbol (link stubs it to nil); LLVM used to reject it. LLVM now matches
Cranelift (parity), but both are wrong at runtime for that path: the receiver
type is a type-inference/lowering gap (trait value should lower to
MethodCallVirtual), not a missing builtin entry. Fixture:
test/native/llvm_builtin_parity (None path only). Open: lower trait-typed
Option payload receivers to virtual dispatch.
