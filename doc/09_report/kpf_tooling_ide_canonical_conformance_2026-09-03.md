# KPF Tooling/IDE Canonical Conformance — 2026-09-03

## Scope

This lane advances the editor-neutral tooling requirement without changing
compiler bootstrap or Phase 7 qualification. It covers canonical result
identity, stale-result rejection, cancellation, document close, connection
cleanup, and explicit degraded/unavailable states in native SVIM and VS Code.

## Implementation

- `lint_output_canonical_result_id` derives one deterministic `kpf-result-v1`
  identity from verdict, provider receipt, input revision, completed coverage,
  and diagnostic count.
- The toolingd LSP edge returns that identity as both a typed field and the
  `canonicalResultId` JSON member consumed by editor clients.
- Edge-level `close_document` and `disconnect` cancel and erase owned analysis
  tickets before delegating lifecycle closure to the daemon.
- SVIM now closes and disconnects through those edge lifecycle operations.
- VS Code requires the canonical identity, cancels superseded snapshots, and
  clears all snapshots on disconnect while publishing `Unavailable` state.

## Evidence

| Check | Result |
|---|---|
| Pure-Simple SVIM focused spec | PASS, 5 passed / 0 failed |
| Toolingd document-session protocol | PASS, 5 passed / 0 failed |
| Toolingd edge protocol adapters | PASS, 4 passed / 0 failed |
| VS Code KPF host cases | PASS, 9 cases |
| TypeScript compilation and webview build | PASS |
| Mutated noncanonical result identity | Rejected without publication |
| Direct environment/runtime boundary guard | PASS |
| `doc/06_spec` executable placement count | 0 |

The full VS Code GUI run reached the extension host and recorded 15 passing
tests, including all nine KPF cases. Ten unrelated tests failed because the
test host opened without a workspace folder; those failures do not contradict
the focused KPF results and are not claimed as passing.

## Remaining Work

- Repair or configure the repository-wide VS Code workspace fixture so its
  unrelated workspace-dependent GUI cases can run.
- Execute browser/Wasm client parity and representative tooling latency/RSS
  qualification before final KPF completion.
