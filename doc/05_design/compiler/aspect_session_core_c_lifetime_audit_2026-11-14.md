# AOP session cache: core-C lifetime source audit

Status: source audit, not native execution qualification.
Audited feature head: `c56a3664265`; release integration checkpoint: `55f23cca055a`.
Scope: the owned core-C runtime and the inspected ordinary native LLVM/Cranelift
assignment paths. This does not qualify an alternate runtime or future GC pass.

## Overwriting an invalidated slot

`50.mir/mir_lowering_stmts.spl:2313` lowers a plain global assignment to
`StoreGlobal` at line2369. It does not load or drop the old value; the compound
assignment branch is separate. LLVM's `translate_store_global` at
`70.backend/backend/_MirToLlvm/core_codegen.spl:3499` emits a direct store.
The flattened variant at line3538 likewise emits `store` of the new operand.
Cranelift's `StoreGlobal` arm in `cranelift_codegen_adapter.spl:808` resolves the
slot and stores the new operand without loading or releasing its prior payload.

Ordinary field assignment ends in `emit_set_field` at
`50.mir/mir_lowering_stmts.spl:2736`; its optional isolated-place move concerns
the incoming value. `mir_data.spl:1881` emits `SetField` directly. LLVM's
`_MirToLlvm/aggregate_intrinsics.spl:333` computes the field address and stores
new bits. Cranelift's corresponding arm at line848 does the same. Thus the
inspected CompileContext cache-slot replacement does not inspect its old graph.

## No automatic global-root tracing in this owner

`src/runtime/runtime_native.c:3309` explicitly documents that this runtime has
no write barrier, including direct raw-struct field stores. Session end at
line3582 iterates the session allocation list, reclaiming objects still tagged
with that session; it does not traverse program globals or CompileContext.
The session/scope ID allocator at line3554 refuses exhaustion rather than
reissuing zero/wrapped identities.

The owned runtime's graph collectors, including `core_rc_collect` at line10127,
start from an explicit caller-supplied root and follow its children. Searches
for GC collection, global-root registration and global scanning in the owned
runtime found no automatic global-root scanner. This source inspection is
bounded to this runtime, not a universal assertion about linked foreign code.
The actual BuildSession keep path retains selected result/diagnostic fields,
not the entire CompileContext graph.

Consequently the scalar initialized/session guards can leave an invalidated
slot unread until replacing it under a live owner in this admitted source
configuration. Reset must occur before freeing the session, must allocate
nothing (not even a boxed None), and must clear the scalar initialized flag.
The cached entry point refuses active/paused transient scopes. Explicitly
walking an ended session's whole context or old cache object remains invalid;
the scalar guard does not make arbitrary graph traversal safe.

Native two-session tests are still required. Any new destructor insertion,
write barrier, global-root tracing, or different runtime invalidates this audit
and requires revisiting the lifecycle seam.

## Nullable collection receipts (#9226)

Release `bb2a83ed4da` changes three raw Linux process receipt functions to
`[i64]?` and maps absence to an error retaining the same process lease.
The public owner methods continue returning their existing Result types.
The AOP traversal, snapshot and kernel-image owners do not call these raw
receipt functions. No F1 caller signature change is required. The managed
process/broker route benefits from truthful unavailable-receipt handling;
this delta does not provide body, image, or cache lifetime authority.

## Separate unresolved dependency

The inherited kernel-image memo directly stores digest text captured inside a
build session in process globals. Its owner independently confirmed this
lifetime risk and is fixing it separately. This AOP source audit does not fix
or qualify that memo. Warm runtime admission remains blocked until that owner
fix and the authored native tests are qualified.
