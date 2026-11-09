# trace_seed_interp_refuses_owned_process_v3_2026-11-06

- **Status:** fix-implemented-verification-pending (2026-11-08)
- **Severity:** P2
- **Spec:** test/03_system/app/traceability/feature/trace_query_p0_spec.spl

## Finding 2026-11-08

The owned-process V3 adapter landed in PR #7214
(`src/compiler_rust/compiler/src/interpreter_extern/process_owned_v3.rs`,
`src/runtime/runtime_process_owned.c`). No further seed code change is needed;
the failure is the stale deployed `bin/simple.exe`.

Measured on Windows, same worktree at `origin/release/1.0.0`:

| binary | `trace list requirements --snapshot=git:HEAD --format=sdn` |
|---|---|
| deployed `bin/simple.exe` | `status: error, code: TRACE-QUERY-INFRASTRUCTURE, "owned process start: invalid 4-word receipt"`; spec reports `OwnedProcessV3 opaque adapter is unavailable in the interpreter` |
| seed freshly built from release head | `capture: immutable-git-tree, graph_complete: true` (rc 0); the adapter error no longer appears in the spec run |

Remaining spec failures with the fresh seed are worktree-capture/SDN errors
from a sparse, symlink-less Windows checkout, not the adapter.

**Verification needed:** redeploy the seed (`bin/simple.exe`) and re-run the
spec on a full checkout.
