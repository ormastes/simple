# Direct LLVM-C ABI prerequisite

Authored 2026-10-03. This prerequisite does not implement or certify a JIT.

The pinned LLVM 23.1.1 SDK exposes fixed C functions for pointer handles,
pointer out parameters, signed 32-bit LLVMBool, unsigned version outputs and
void results. Canonical declarations belong under nogc_sync_mut/sffi and must
be explicitly unsafe with ffi/raw_ptr capabilities. No dynamic all-i64 call
adapter, text-to-C conversion, or compiler leaf extern is part of this boundary.

Before declarations are usable, actual frontend -> HIR -> MIR -> LLVM tests
must preserve the declared fixed signature at both the direct call and external
declaration. Current direct call lowering constructs an empty parameter list;
the LLVM backend ignores that list and emits a variadic external declaration.
Tests below expose this prerequisite without modifying lambda ABI producers.

The initial exact subset is resolved fixed extern declarations whose parameters
and results are scalar C-compatible integers or raw pointers, with Unit allowed
only as the result. Text, aggregates, function values, inferred/unresolved
types, and ABI-adapted runtime hooks remain outside this change. Extern identity
must come from resolved declaration provenance, not a spelling whitelist.

The first source repair records only nonempty fixed extern signatures, keyed by
the current module's resolved SymbolId and reset before every lower_module.
The initial value subset is i32/u32/i64/u64 and concrete raw pointers; other
integer sizes are permitted as pointees only. Zero-argument extern declarations
still need explicit empty-signature authority in the LLVM backend, which today
conflates an empty legacy signature with unknown parameter types. Consequently
the complete ORC raw binding owner is not enabled by this repair alone.

Once supported, process linkage uses the existing explicit BuildConfig library
contract. A safe ORC session must separately validate the loaded provider's
actual identity and keep it resident, validate translated MIR's exact scalar
ABI with no imports, and use a shared live-owner identity so closing any copied
session invalidates all copies. Raw addresses are not reusable safe callables.
Concurrent invocation/close requires one proven synchronization owner before
being exposed; no mutable global registry is assumed safe.

LLVMParseIRInContext2 retains caller ownership of its memory buffer on success
and error. LLVMOrcCreateNewThreadSafeModule transfers the module to the wrapper;
AddLLVMIRModule consumes the wrapper on return, including errors. LLVMErrorRef
must be consumed once, and messages freed by the matching LLVM error/message
disposer. These are pinned header contracts, not executed validation.

Admission still requires compiler and native execution tests on the admitted
selfhost runner, exact SDK/provider pairing, and a complete translate/create/
add/lookup/invoke/dispose path with copied-owner and failure tests. Ordinary CLI
JIT selection and collection engine parity remain unchanged.
