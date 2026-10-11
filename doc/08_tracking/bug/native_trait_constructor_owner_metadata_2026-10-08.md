# Native trait conversion loses constructed class owner

Status: source repair only, native regression UNRUN. Base source
`8ccea67adf9cf01c4fe6eccf2ad852ddf4fafcf5`; no admitted compiler/source mutation.

The qualified cycle-2 compiler's LLVM `native_trait_two_owner_dispatch.spl`
build fails MIR with `missing native trait implementation: ...DispatchOwnerProbe
for ` (blank concrete owner) at constructor arguments, explicit/tail returns
and class fields. Retained log:
`build/item5-trait-enum-layout-cycle2-20261008/qualification/llvm/trait-class/build.log`.
Its independent unresolved optional-payload method diagnostic remains visible;
this change does not claim that entire fixture passes.

`lower_struct_construct` has the original resolved HIR constructor SymbolId but
only retained a canonical MIR Struct ID and `struct_value_syms` layout name.
Class layout names are module-qualified `mir_class_identity` strings, not
necessarily lexical symbol-table bindings. The conversion fallback attempted
`symbols.lookup_or_invalid` on that layout key, and cannot recover a declaration
from an erased/untyped constructor expression. MIR canonical IDs are a separate
identity domain and cannot be substituted for HIR IDs.

The construction owner now records plain Named HIR metadata with the original
resolved declaration ID for actual Class/Struct symbols. Existing nominal layout
keys are unchanged. This is declaration identity, not generic argument inference
or isolation erasure: explicit isolation wrappers still have their own admission.
Trait conversion retains exact trait/concrete owner matching and full signature
checks; no implementation-count heuristic or raw-name match is introduced.

New `test/04_smoke/native_trait_constructor_owner.spl` requires six real native
assertions across two implementations and argument/return/field conversion.
Existing missing-implementation, signature and mutability negatives remain
unchanged and must still reject. Existing two-owner and struct-copy/borrow fixtures
remain the wider acceptance rows. No compiler build, native execution or broader
required compiler checks have been performed for this source-only successor.
