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

The source repair records fixed extern signatures, keyed by
the current module's resolved SymbolId and reset before every lower_module.
The initial value subset is i32/u32/i64/u64 and concrete raw pointers; other
integer sizes are permitted as pointees only. Additive MirSignature.params_known
defaults false and is set true from those declarations. Signature copying, JSON
serialization and verification input identity preserve it. LLVM records known
empty lists and emits fixed `()` while legacy unknown lists remain `(...)`.
There is no owned JSON MIR deserializer in the inspected path; serialization
identity is tested without claiming a roundtrip. Same-module lambda lowerers
copy authority; fresh bootstrap lowerers seed only their module declarations.
The complete ORC safe owner is not enabled by this repair alone.

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

## Raw owner and SDK inspection

`src/lib/nogc_sync_mut/sffi/llvm_orc_raw.spl` contains 24 annotated unsafe
direct extern declarations, with no facade aggregation or automatic library
dependency. Handles and pointer outputs remain pointers. The only integer
address is LLVMOrcExecutorAddress's declared uint64_t output; it is not exposed
as a safe callable. MemoryRangeCopy's size_t is represented by u64 only under
the explicit x86_64 SDK precondition. This owner is not portable to 32-bit ABI.

Inspected SDK root:
`C:/Users/user/.simple/toolchains/llvm-msvc-23.1.1/clang+llvm-23.1.1-x86_64-pc-windows-msvc`.
Its llvm-config.h declares 23.1.1. Inspection of its LLVM-C.dll COFF export
table found all 24 declared symbols, including ParseIRInContext2 and the actual
X86 initializer exports; no header-only NativeTarget helper is declared.
Headers consulted: llvm-c/Core.h, Types.h, IRReader.h, Error.h, Orc.h, LLJIT.h.

Observed SHA256, 2026-10-03:

| SDK file | Digest |
|---|---|
| bin/LLVM-C.dll | 1286e894afc98486963246a3f786459b63efb8bd3e4a00193530013fe46aa1fe |
| lib/LLVM-C.lib | f8b52031f1e5b547bb94c7ef7d6a0b00893bcde5ea72cc7bc124ab934d2acad6 |

These hashes describe inspected files, not the provider actually loaded by a
future process. Import-library forwarding does not constrain Windows DLL search
or attest loaded module bytes. The safe owner still needs loaded-provider
identity, initialization synchronization, process residency and shared session
generation/lifetime enforcement before any invocation can be authorized.
No LLVM function was invoked during this inspection; only export/header/file
metadata was read. Compiler ABI specs remain authored and unexecuted.

## Native smoke audit, 2026-10-03

The planned real version/context smoke is blocked by local raw-output storage
and cross-module extern-authority transport. Existing local `&mut` emits a
value borrow identity, not a writable C output slot. The inspected imported
free-function path registers a typed caller symbol but does not carry the
provider's is_extern declaration into the local-only signature registry.
Appending a consumer to the owner source, as the current ABI tests do, does
not prove that an actual import preserves fixed arity. The raw declaration
owner therefore remains unqualified for the requested imported native smoke.

Exact source seams and required storage/import/native acceptance are recorded in
`doc/08_tracking/bug/llvm_native_abi_smoke_storage_and_import_authority_2026-10-03.md`.
No context-only substitute, integer-to-pointer workaround or extra compiler
repair was introduced; this slice performed no native execution.
