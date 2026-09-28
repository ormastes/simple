# Cranelift shared object path blocks Stage 6A byte ownership

Status: OPEN; source-confirmed race, not a reproduced runtime exploit.
Source: `origin/main` at `0dbb2c1691a442829737507dc8d1d2a970bbf7bf`.
Scope: existing Feature A / NFR N2 and Stage 6A.1c. No new selection.

## Evidence

`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` uses
`{_get_temp_dir()}/simple_cranelift_{module.name}.o` in both
`cranelift_compile_module_direct` (line 183) and
`CraneliftCodegenAdapter.compile_module` (line 245). Each emits, frees the
module, then reads that shared path. Concurrent compiles with equal module
names can overwrite it between emission and capture; the pathname also embeds
caller-controlled module text. Neither path owns private staging or removes
the output.

`src/lib/nogc_sync_mut/sffi/codegen.spl:506` exposes file emission only.
`src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs:1809` implements it by
removing the module from `AOT_MODULES`, finishing it, emitting bytes, and writing
the caller path. Thus emission itself consumes the live ISA/module even on
write failure. Moving the later Simple `free_module` call is insufficient to
preserve its lifetime. This native source was inspected only; no Rust seed was
executed or used as verification.

The adapter's `cranelift_new_aot_for_request_v2` already checks live ISA feature
and optimization readback but discards those observations. The public compile
APIs return `Result<CodegenOutput, CompileError>` without a retained cleanup
lease. `backend_plugin/session_authority_v2.spl` correctly remains `Unknown`
and rejects feature-bearing requests.

## Required implementation boundary

Introduce a retained compile-output owner shared by the direct, adapter, AOT,
and session routes. Before consuming emission, retain provider observations
from that same live module. Prefer a provider-owned in-memory emission result;
the current Simple API does not expose one. A file implementation needs a
private directory generated independently of module text, a fixed child name,
bounded exact-byte capture, and an owner retained until cleanup completes.

The owner must distinguish module-live, emission-consumed, bytes-captured,
cleanup-pending, and retired states. Emission is single-use. Failure to emit,
read, validate, or clean up must not publish an accepted result. Cleanup failure
must preserve the only lease for a later retry; an ordinary error string or
process-global list of paths is insufficient ownership. Cancellation must stop
new work and retain the lease until in-flight provider access has ended, then
clean up in reverse acquisition order. Session close must refuse or retain
cleanup-pending results rather than dropping their owner. Retry must never
repeat consuming emission or release a module twice.

This requires plumbing an owned outcome through the existing result boundary
or adding provider-owned memory emission. A local temporary-directory patch
alone cannot meet that cleanup contract. LLVM and dynamic V1 stay `Unknown`;
Cranelift also stays `Unknown` until a live provider result binds confirmed
configuration to these exact bytes.

## Falsifiable verification plan

1. Compile two real modules with the same name but distinguishable functions;
   synchronize emission/capture overlap. Each result must contain its own
   function/body and use a different private artifact identity.
2. Precreate the old shared pathname with sentinel bytes and exercise module
   names containing path separators. The sentinel must remain unchanged and
   never be returned as compiled output.
3. Inject emission failure and read/truncation failure after real provider
   emission. No result token is published; module consumption occurs once.
4. Force cleanup failure, observe a retained cleanup-pending lease, restore the
   filesystem, and retry close. The private artifact disappears and its owner
   retires exactly once. New compile use is refused while closing.
5. Cancel before emission, during provider work, and after capture. Verify no
   early artifact removal, lost lease, duplicate emission, or double release.
6. After ownership passes, test feature readback/configuration substitution and
   byte substitution through the real provider/session boundary. A synthetic
   receipt or caller-supplied digest is not production evidence.

No production code changed and no runtime test was executed for this report.
