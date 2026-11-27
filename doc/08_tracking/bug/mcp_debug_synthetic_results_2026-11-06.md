# MCP debug synthetic results — 2026-11-06

Owner: release100_memory_mcp_lsp / debug_truth.
Status: implementation prepared; source review completed; executed verification pending.

## Reproducer and boundary

Create an OpenOCD configured session (no target is attached), then call the actual MCP lazy handlers for stack trace, evaluate, continue, step, variable mutation, watches and breakpoints. Before repair, src/app/mcp/main_lazy_debug_tools.spl constructs a main frame at line 1, echoes evaluation input, returns empty variables and claims successful mutation/verified breakpoints without a backend response. src/app/mcp/dap_bridge.spl registers DebugServiceV1 target verification as Unverified and only retains breakpoint strings. This proves the defect is in the pure-Simple adapter; no runtime change is needed.

## Required repair

Return explicit unsupported tool errors with canonical policy/outcome receipt and no target-state mutation. Keep transport/session registration distinct from attachment. Hardware bootstrap-plan responses must identify that no operation executed. Preserve disk-source reading and actual session cleanup. A future admitted DebugWire transport must replace the unsupported path using real target identity, stop epoch and backend outcome.

## Verification

Pre-fix source path inspection reproduces the unconditional fabricated returns. Executed regression is pending an admitted full pure-Simple runtime; no deployed legacy binary is accepted as release evidence. Exact and adjacent regressions use real handlers with a configured, unattached target and a missing session.

## Remaining scope

Real assertion stop interception, worker/fiber frames, variable snapshots, watchpoints, control leases, epoch invalidation, remote transport and shared screen/REPL parity remain open. This truthfulness repair does not complete DBG-01 through DBG-10.

## Review evidence

Independent memory_audit review found no P0/P1 in changed handlers. Its duplicate
authorization observation was repaired by reusing the first denial receipt.
Scoped `git diff --check` passed before the final unused-import cleanup.
No execution, live target or release verification PASS is claimed.
