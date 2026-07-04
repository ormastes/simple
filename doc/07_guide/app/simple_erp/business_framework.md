# Guide: Simple ERP Business Framework

How to run, extend, and verify the business suite in
`examples/12_business/simple_erp/`.

## Run everything

```bash
bin/simple test examples/12_business/simple_erp/ubs_test/ --mode=interpreter   # 21 unit specs
bin/simple test test/03_system/app/simple_erp/feature/ --mode=interpreter      # 4 system specs
bin/simple examples/12_business/simple_erp/src/business_suite.spl              # per-lane gate evidence
bin/simple examples/12_business/simple_erp/src/dashboard_main.spl              # HTML dashboard
bin/simple examples/12_business/simple_erp/src/bigbiz_demo.spl                 # big-business mechanics
```

Verification caveat: grep spec output for `✗` / `N failures`, not just `PASS` —
the interpreter runner's file summary can report green despite failing
examples (tracked bug: `doc/08_tracking/bug/test_runner_interpreter_file_summary_greenwash_2026-07-03.md`).

## Add a new business (3 steps, zero framework edits)

1. Write a lane module in `src/lanes/<name>.spl`: domain structs + a
   `validate_*` verdict + a `submit_*_write` that calls
   `gate_write_for(lanes, session, tenant, user, "<name>.write", valid, key, used_keys)`.
2. Register it where your app builds its registry:
   `lanes.push(lane_def("<name>", "/api/<name>/...", threshold_minor, approver_role))`.
3. Done. RBAC (`role_can_for`), routes (`routes_for`/`dispatch_for`), gating,
   and dashboard cards derive from the registry.

Working example: `src/extension_demo.spl` adds a clinic lane this way.

## Policy is data

- Roles: `framework/org.spl` `RoleDef` (`all_actions` superuser, `writes_lanes`
  grant, `extra_actions` closed set). The gate's `role_can_for` delegates to
  `org_role_can(default_roles(), ...)` — one RBAC source.
- Approval: `gate_write_with_approval` denies `needs-approval` at/over a
  threshold without the approver role; ordered sign-off via `ApprovalChain`.

## The gate contract

Every write: session → RBAC → validation → idempotency. Closed reasons:
`accepted | invalid-session | forbidden | invalid-record | duplicate-key | needs-approval`.
Lanes never re-implement this sequence.

## Kernel guarantees

- Event log is the only write point; ledger balances are projections
  (`kernel/projection.spl` — Σ signed lines == 0).
- Persistence: `kernel/durable_log.spl` — escaped line format, injective
  checksum, load fails closed to an EMPTY log on any mismatch.
- Volume: `kernel/snapshot.spl` (snapshot+tail == full replay),
  `kernel/key_index.spl` (bucketed idempotency).
- Concurrency: `kernel/commit_queue.spl` — per-tenant FIFO, atomic drain.

## Status vs SAP

See `doc/01_research/domain/simple_erp_vs_sap.md`. Mechanics parity at example
scope; not a production system until the event log sits on a real store,
posting is mandatory on accepted writes, and the runner bug is fixed.
