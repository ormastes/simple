# Windows Full Bootstrap and Toolchain Suite — TLDR

Windows bootstrap is a monotonic, receipt-driven state machine. Each phase consumes one immutable admitted parent and emits a hash-bound subject; build, verification, publication, deployment, and rollback are separate authorities.

## Core Shape

- `Frozen -> Built -> Verified -> Admitted -> Published -> next phase`.
- Eight capsules isolate source freeze, build, admission, Stage 3, Stage 4, suite evidence, publication, and deployment.
- Missing/stale/cross-generation evidence, fallback, source drift, or ambiguous identity fails closed.
- Stage 4 deploys one immutable generation via an atomic pointer; rollback compare-selects a verified predecessor.

## Operational Notes

- MCP/LSP hot paths reuse digest-keyed indexes; no repeated full-tree scan or per-request compiler subprocess.
- Evidence binds warm startup, request p50/p95/max, max RSS, fixtures, and exact binary hash.
- Identical failed commands are not repeated; one issue has at most three distinct fix cycles.

## Open Next

- [Full architecture](windows_full_bootstrap_toolchain_suite.md)
- [Detail design](../05_design/windows_full_bootstrap_toolchain_suite.md)
- [System-test plan](../03_plan/sys_test/windows_full_bootstrap_toolchain_suite.md)

