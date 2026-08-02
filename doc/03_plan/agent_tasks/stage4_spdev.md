# Stage 4 SPipe agent tasks

## Active lanes

| Lane | Scope | Status |
|---|---|---|
| Correctness | Incremental Stage 3 refresh; Stage 4 HIR/import failures; exact and adjacent regressions | Awaiting fresh run from `545a6c297248` |
| Performance | Phase timing/RSS, retained compiler graphs, safe pure-Simple optimizations | Sol-high compact-surface change pushed; measurement pending |
| Cache | Producer and dependency fingerprint correctness | Blocked on complete canonical MIR and direct-interface hashes |
| Host/ABI | Linux/macOS/Windows/BSD/SimpleOS and x86_64/AArch64 deallocation contracts | Current scoped contracts pass |

## Coordination

- Merge owner: primary Codex agent in the main integration workspace.
- Final reviewer: normal/highest-capability Codex after the exact fresh Stage 4
  binary passes the required smoke gates.
- Agents claim bugs before edits and announce owned files before overlapping
  compiler work.
- A Stage 4 session permits at most three distinct fix/verify cycles; identical
  failed commands are not rerun.

## Completion evidence

- Fresh Stage 4 native-build PASS log and progress/RSS log.
- Exact artifact path and SHA-256.
- Exact-binary sanity PASS.
- `check-bootstrap-essential-tools-smoke.shs` markers for test-runner, lint,
  duplicate-check, and aggregate PASS.
- Deployment record and rollback path.
- Updated session plan with no obsolete blocker or missing artifact link.
