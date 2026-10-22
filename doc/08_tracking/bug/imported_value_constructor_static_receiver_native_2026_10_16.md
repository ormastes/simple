# Imported Value constructor receiver on baked native producer

2026-10-16. Source candidate only; native verification UNRUN; DB reconciliation
pending. Recovery base67ba74d9acbaa998d5efcb3c162bf61a63f839d0.

The retained exact0CD6 main compiler attempt reports undefined Value receivers
and unresolved Bool/Int/Float/etc calls in actual interpreter consumers. The
actual enum owner is src/compiler/70.backend/backend_types.spl, not the nested
backend/backend_types API-type provider. A fix to newly authored lowering source
does not update the baked producer executing this bootstrap.

The source candidate adds genuine top-level typed factories beside the original
Value declaration and explicitly exports them. They construct the ORIGINAL
Value variants with the ORIGINAL argument/payload types. Actual interpreter,
binop, calls and expr source constructor calls become ordinary imported factory
calls. Qualified Value patterns remain unchanged. No replacement enum, invented
runtime ID, bitcast, direct rt_enum_new, runtime stub, or flattened compiler
symbol is introduced. Each original argument expression occurs once in the
same order. Four inverse rewrites reconstruct the complete original consumer
files after removing only tags/imports and restoring call names.

There are82 constructor expressions in these four actual consumer files and12
used payload variants. These source counts are not the count of retained main
diagnostics. Unchanged Value unit accesses, other static methods and other
consumer modules are outside this rewrite and may remain independent failures.

The native fixture imports the real Value owner and a second genuine overlapping
SdnValueKind declaration. Primitive and nested array/tuple/dictionary/struct
payloads are checked through original Value patterns. Function/closure/object
and opaque pointer cases test declared carrier fields only: arbitrary symbol
and object handles are NOT proof of callable functions, allocated object-store
membership or foreign RuntimeValue dereference. No foreign pointer is used.
Reference/alias semantics beyond input preservation require actual full
interpreter acceptance, not this carrier probe.

The actual owner now imports only the terminal data definitions it uses:
HirExpr/HirParam, SymbolId and MirTypeKind (MirType was already explicit).
This genuine dependency correction replaces two engine-facade globs; the
existing explicit export surface is preserved. No Value body or declaration
is removed to shrink the probe. Two further actual optional/result factories
bring the cohort to14; original some/none/ok/err methods delegate to those
same factories with typed optional locals. The probe exercises Some/nil
presence and exact contained Value fields through the ordinary functions.

This is the SAME constructor feature whose earlier engine qualification attempt
failed with496 unrelated MIR fatals. At most two further verification cycles
remain within the shared maximum3; there is no renamed-feature reset. No build
before source/fixture review and freeze. A passing old-producer helper probe
would not qualify a new lowering implementation. The required final target is
actual full interpreter/backend_types/binop/calls/expr compilation in canonical
context, collecting every remaining failure. No object/context graft.
