<!-- codex-design -->
# Agent Tasks — Dashboard Crash Containment Framework

Date: 2026-04-03

1. Audit the current local crash-policy and dashboard worker code paths.
2. Compare Rust panic semantics with Erlang, Go, Java, and Node primary-source models.
3. Align repo defaults with explicit user-selected hosted vs heavy vs bare-metal policies.
4. Patch worker launch to propagate runtime budgets into child environments.
5. Fix the current dashboard crash path before broader framework rollout.
6. Validate targeted policy tests in Docker.
7. Validate a current `simple dashboard` command path in Docker.
8. Keep build/test/verification on Docker paths so the dashboard fix cannot be invalidated by host-environment drift.
9. Record residual risks:
   stale system test pathing, compose/doc drift, and incomplete structured crash telemetry.
10. Keep dashboard-specific supervision work scoped to hosted workloads and defer bare-metal panic/watchdog policy to the generic framework path.
