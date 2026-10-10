# Native trait method lookup through copied SymbolId keys

Status: identity-index source repair; native regression UNRUN. General native
aggregate dictionary-key equality remains an open compiler/runtime defect.

The retained ec7 counter HIR has matching trait/implementation signatures and
exact method IDs 11/12. Nevertheless native admission fails. Disassembly at
0xa6c9be–0xa6ca80 copies the returned SymbolId into fresh `rt_alloc` storage,
tags it, and passes that aggregate to `rt_index_get(module.functions, target)`.
This is not the original dictionary key allocation. The actual Rust dictionary
owner's structural object hashing applies to registered RuntimeObject values;
the generated raw one-word aggregate copy is not such an object.

Registration now indexes the module's declaration values once by their scalar
`declaration.symbol.id`, then resolves each implementation target's exact ID
to the corresponding array position. Duplicate IDs cause a fatal diagnostic;
missing IDs retain the empty-callable admission failure. No method-name fallback
or signature relaxation is used. This also avoids an optional HirFunction
aggregate round-trip through the dictionary lookup result.

This metadata index does not fix general `Dict<SymbolId, ...>` value-key
semantics. A separate minimal copied-aggregate key runtime/compiler regression
and representation repair are still needed; do not report that language issue
resolved by this index.

Retained source/binary review: `build/review/item5-trait-registration-key-review-20261008.md`
and `item5-trait-register-ec7-20261008.disasm`. Existing native counter fixture
must be rerun with the next qualified compiler; no pass is claimed here.
