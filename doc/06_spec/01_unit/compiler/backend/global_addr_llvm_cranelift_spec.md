# LLVM and Cranelift module-static address contract

This executable contract proves that `GlobalAddr`, `Load`, and `Store` use one
canonical module-static declaration rather than allocating or copying storage.

## LLVM

1. Create one public, 32-byte-aligned `i64` static initialized to 29.
2. Materialize its address, load through that address, and store back through it.
3. Confirm all operations name the same LLVM global.
4. Confirm private globals use `internal` linkage and scoped globals use
   `hidden` linkage.
5. Source-contract coverage confirms bootstrap dispatch reads nested `LocalId`
   and `SymbolId` payloads through typed accessors, resolves the bootstrap
   static accumulator, and diagnoses a missing static instead of fabricating
   invalid LLVM. This is structural coverage, not executed bootstrap evidence.

## Cranelift

1. Confirm all six source visibility states map to Export, Hidden, or Local
   without collapsing scoped visibility to public export.
2. Confirm explicit alignment wins and zero selects natural alignment.
3. Confirm `GlobalAddr` uses the same declared-data handle as global load/store.
4. The provider-side executable test calls the address function twice, checks
   pointer identity and 32-byte alignment, reads the initializer, writes through
   the first pointer, and observes the update through the second pointer.
5. Provider executable coverage rejects invalid linkage, negative alignment,
   non-power-of-two alignment, and alignment above the documented 4096-byte
   bound. Simple adapter mapping coverage is executable when this spec runs;
   it is not claimed as measured in this no-verification handoff.

No runtime allocation is performed by `GlobalAddr`; it materializes an SSA
address for the module data declaration already owned by the backend.
