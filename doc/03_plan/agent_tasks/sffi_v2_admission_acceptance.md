# Agent tasks: SFFI v2 admission acceptance

**Status:** `developing` — acceptance tests first  
**Merge owner:** `/root`  
**Final reviewer:** highest-capability Codex reviewer

## Frozen shared contract

Categories, runner names, and manual-step/checker names are frozen in
`doc/05_design/sffi_v2_admission_acceptance.md`. Every lane keeps source-only
evidence separate from artifact admission and makes no hot-path change.

| Lane | Scope | Sidecar | Status |
|---|---|---|---|
| A1 | modern SSpec acceptance fixture/scenario scaffold | N/A | developing |
| A2 | fixture manifest/trust/receipt matrix and runner seam | N/A | developing |
| A3 | loader/inventory typed-result handoff and no-hot-path gate | N/A | developing |
| A4 | direct `rt_*` backlog prioritization + exact autofix contract tests | N/A | developing |

Each lane works in a separate worktree, commits only owned files, does not
push, and returns a failing blocker rather than a fabricated PASS. A1 starts
the executable `@tag("developing")` SSpec before any implementation promotion.
