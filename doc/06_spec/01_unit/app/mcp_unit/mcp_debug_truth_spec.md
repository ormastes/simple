# MCP debug operation truthfulness

Status: authored operator outline; generation and execution pending admitted runtime.
This is not a generated PASS receipt.

## Verification

`test/01_unit/app/mcp_unit/mcp_debug_truth_spec.spl` invokes actual lazy handlers
with a configured but unattached OpenOCD target. It covers synthetic observation
rejection, side-effecting expression refusal, unchanged state, absent
breakpoint/watch mutation, hardware plan labeling, invalid input, and closed
central authority. No target process or hardware is started by that fixture.
Execution, generated-manual validation and release gates await an admitted
full pure-Simple runtime; source review is not an execution PASS.

## Operator scenarios

1. Register an unattached target, then request stack and locals: expect explicit
   unsupported errors and no fabricated observation arrays.
2. Evaluate a side-effecting expression: expect refusal, without an echoed value.
3. Continue, step, set a variable and terminate: expect refusal and unchanged
   session metadata; explicit close remains available afterward.
4. Set/enable/remove source, function and data breakpoints: expect refusal,
   unchanged local intentions and no verified target breakpoint.
5. Add/list/remove watches: expect refusal and no invented historical value.
6. Request hardware flash: expect unsupported, plan-only bootstrap metadata and
   a no-change receipt; nothing reaches hardware.
7. Use missing sessions or invalid modes: expect precise parameter errors.
8. Close the central authority while retaining adapter metadata: expect denied,
   proving stale metadata cannot confer control.
