# Native extension-method call omits a default argument

Status: repair implemented; native qualification pending.

The refreshed Windows Phase 2 LLVM and Cranelift compilers build successfully,
but their Hello World compilation workers exit with an access violation before
claiming a HIR module. This is not a linker failure or a failed source-module
diagnostic.

The retained LLVM capture identifies a null request dereference in
`native_entry_closure_request_open_v1`. Its ancestor calls
`CompilerDriver.load_sources_impl()` with only the receiver register set,
although the method now declares `preclosed: NativeEntryClosureRequestV1? = nil`.
The callee consumes the unset argument register. The optional-value predicate
must not be weakened: raw zero is not the runtime's nil sentinel, and valid
`Some(0)` and `Some(false)` values must remain present.

Native project linkage can find an extension method defined in another source
module even when that module's declaration has not been visited by the caller's
import loader. The native import map supplied method arity and return metadata,
but did not supply the default expressions needed to complete the caller's ABI.
The existing direct-import default collector therefore does not cover every
native extension-method call.

The repair collects defaults under the actual mangled method symbol, publishes
only unambiguous `Owner.method` contracts to HIR, and uses them after explicit
local/imported contracts. Shared immutable metadata avoids copying the map for
every module. Defaults participate in the cross-module fingerprint so changing
a default also invalidates cached callers.

Regression coverage includes a separately defined extension method called from
another module, preservation of explicitly supplied arguments, rejection of
ambiguous owner defaults, and cache invalidation when a default changes.
Native fixtures additionally cover absent and present records, returned options,
and present zero/false values. Tests are not reported as passing until their
actual results are available.

Evidence is retained under the local bootstrap packet
`windows-restart-20261004/llvm-hir-worker-av-proof2/`, including input hashes,
process closure, registers, stack, unique object-code mapping, and
`root-cause-evidence.md`. The old failed caches and original bootstrap producer
remain unchanged. A new bootstrap producer and Phase 2 rebuild are required to
validate the repair; source review alone does not establish Phase 3/4 success.
