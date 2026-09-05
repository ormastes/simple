# MCP Failure Prevention System Test Plan

## Scope

Prevent recurrence of MCP failures across five boundaries: pure-Simple
interpreter startup, JIT runtime-symbol registration, wrapper/native artifact
admission, live MCP/LSP protocol and representative tool calls, and warm
startup/request/RSS budgets.

Executable spec:
`test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl`.

## Shared test vocabulary

- Runner: `run_mcp_gate(program, args, timeout_ms)`.
- Pass checker: `check_gate_pass(result)`.
- Evidence checker: `check_marker(result, marker)`.
- Operator steps:
  1. `Verify interpreter source loading stays bounded`.
  2. `Verify wrappers admit only hash-bound native artifacts`.
  3. `Exercise MCP and LSP protocol functions`.
  4. `Measure warm startup, request latency, and RSS`.

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-MCP-CMD-001 | Interpreter lazy-load and JIT-symbol contract, plus native MCP functional smoke |
| REQ-MCP-CMD-002 | Wrapper contract, SHA-256-bound fresh artifacts, correlated MCP/LSP calls |
| REQ-MCP-001 | MCP inventory/schema and request-ID markers from native smoke |
| REQ-MCP-003 | Bounded wrapper subprocess policy and live tool-call results |
| REQ-MCP-005 | MCP and LSP representative family calls plus NFR sessions |

## Failure matrix

| Point | Required failure signal |
|---|---|
| Interpreter starts scanning the full project | Source contract fails; fresh runtime gate exceeds normal guard |
| JIT file probe is absent | Runtime-symbol contract fails before fallback can be accepted |
| Native artifact or sidecar is missing/stale | Wrapper/native smoke exits nonzero |
| Framing, schema, request IDs, or tool call regresses | Corresponding native-smoke marker is absent |
| Probe cache admits stale identity | `mcp_stale_stamp_reprobe_ok` is not true |
| Startup/request/RSS budget regresses | NFR checker exits nonzero and omits final pass marker |
| NFR configuration is invalid | Exit 2 with `error=invalid_sample_count` |

## Execution

```bash
bin/simple test test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl --output doc/06_spec --no-index
```

The spec is release-blocking. Missing native artifacts, source/Rust fallback,
timeouts, signal exits, placeholder assertions, or absent evidence markers are
failures rather than skips.

## Coordination

- Sidecar lanes: N/A; this is one aggregate contract over existing canonical gates.
- Merge owner: Codex `/root`.
- Final reviewer: Codex `/root` after fresh pure-Simple deployment.
