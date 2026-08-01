# Release Beta Agent Tasks

| Lane | Owner | Inputs | Output | Merge order |
|---|---|---|---|---|
| Requirements/architecture | `/root` | selected B/B | final requirements and design | 1 |
| Compiler facade traversal | `/root` | Stage 3 failure and perf probes | bounded HIR fix + regression | 2 |
| Readiness contract/spec | `/root` | receipt schema | checker, SSpec, manual | 3 |
| Workflow/platform repair | `/root` | latest failed run | fail-closed matrix and passing jobs | 4 |
| Bootstrap/verification | `/root` | merged main WC | Stage 4/5/6 receipts and verify PASS | 5 |
| Release/tag/push | `/root` | verified release | commit/tag; push after approval | 6 |

Sidecar lanes: N/A because the available runtime exposes no requested lower-model sidecar. Merge owner and final highest-capability reviewer are `/root`. Shared interfaces and step/checker helper names are recorded in `.spipe/release_beta/state.md`; any unresolved placeholder must use `assert(false)` or `fail(...)`.

Concurrent dirty files remain owned by their active lanes unless explicitly incorporated after review.
