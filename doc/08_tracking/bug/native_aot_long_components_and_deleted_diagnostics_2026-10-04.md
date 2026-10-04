# Long native object names and deleted failure diagnostics

Status: source repair and regressions prepared; native execution pending.

## Observed failures

The Windows `compile-policy-native-validation/build.log` reports LLVM IR kept
at `simple-aot-diagnostic-*/message.module.ll`, but the caller subsequently
removes that directory. `llvm_object_stage_fail` correctly copies the IR out
of backend staging; the driver deletes its destination in every nonzero-status
return arm. Success with an invalid object also removed diagnostics before
validating the output.

The failing module identity is 263 characters. The former object leaf appends
that identity to the output-base leaf and `.o`, exceeding the Windows component
limit even with extended paths. The independent physical probe at
`runtime/windows-restart-20261004/aot-component-limit-probe/result.json` creates
a 255-character component and fails with an IOException for 264 characters,
both using extended paths. This is evidence for the component defect, not a
native validation result for this patch.

## Repair and ownership

`native_aot_object_path_v1` hashes length-framed output-base and module identities
to one 70-character ASCII leaf. All three emit paths and capsule freezing use
the same owner. The human module name remains in capsules, identities and
diagnostics. Capsule identity already binds the object path, so changed paths
invalidate old capsule receipts rather than silently admitting old objects.
Old cache files and failed attempts remain untouched. Publication semantics,
source authority, provider receipts and backend validation are unchanged.

Backend failure or a missing, nonregular or empty output retains the private
diagnostic directory; the driver logs its concrete path separately from the
potentially corrupt error payload. Only successful, validated publication
cleans that attempt's directory. No global retention scan, automatic retry or
cross-attempt eviction is introduced. The existing message read is bounded at
4096 bytes, but preserved LLVM IR and accumulated failed directories do **not**
have an aggregate disk quota. They belong to the build evidence owner until
explicit cleanup; this patch does not claim bounded disk retention.

## Regression coverage and limits

`native_aot_artifacts_spec.spl` writes and reads two distinct objects with
263-character source identities, verifies deterministic bounded filenames,
preserves actual message/IR files across a failed backend status with a stale
object, cleans only successful diagnostics, and retains missing/empty-output
evidence. The capsule receipt spec verifies the freezer uses the exact same
path owner and preserves the module identity. These four new cases are
prepared, not executed. Native/core/MCP qualification remains pending the next
resource-admitted candidate. No live source or existing receipt was modified.
