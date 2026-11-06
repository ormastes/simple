# MCP debug operation truthfulness

The lazy MCP debug adapter registers target metadata and can return bootstrap
plans. Neither registration, process spawn nor a selected backend proves a
live target handshake. Session output therefore carries
`target_verification=unverified` and `target_operations_available=false`.

Target operations currently return an MCP tool error (`isError=true`) with
`status=unsupported`, or `status=denied` when the shared DebugServiceV1 policy
does not authorize the request. The response binds the session/build/backend,
operation and canonical receipt ID; `execution_changed=false`. Authorization
alone never becomes a successful execution result. The receipt is returned to
the caller; this adapter does not claim a durable evidence ledger.

This applies to frames, locals, evaluation, resume/step/terminate, variable
mutation, all breakpoint operations, and watches. No synthetic main frame,
echoed expression value, empty captured-variable list or verified breakpoint
is returned. Unsupported target termination leaves the registry unchanged;
`debug_close_session` separately closes the actual adapter transport/session.

Hardware helpers retain bootstrap metadata with `plan_only=true` and an error
status. They never claim to flash, reset or capture data. `debug_get_source`
reads current disk and explicitly sets `source_origin=current_disk` and
`target_source_verified=false`; it is not a build-pinned target snapshot.

## Pending admission

Real target request/response transport, authenticated DebugWire routing,
stop-epoch identity, control leases, live data watchpoints, build-pinned source,
and durable evidence export remain open. The full source improvement plan's
DBG-01 through DBG-10 are not passed by this refusal behavior. The separate
legacy/library MCP adapters are not converted by this change.

## Verification

`test/01_unit/app/mcp_unit/mcp_debug_truth_spec.spl` invokes actual lazy handlers
with a configured but unattached OpenOCD target. It covers synthetic observation
rejection, side-effecting expression refusal, unchanged state, absent
breakpoint/watch mutation, hardware plan labeling, invalid input, and closed
central authority. No target process or hardware is started by that fixture.
Execution, generated-manual validation and release gates await an admitted
full pure-Simple runtime; source review is not an execution PASS.
