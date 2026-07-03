# Simple ERP example

Example planning module for a Simple ERP with two operator modes:

- Easy mode: guided CRM, reservation, and selling workflows for small teams.
- Pro mode: detailed operations, approval, accounting, inventory, and audit views.

Current scope is an in-memory Simple implementation: feature catalog, CRM lead
stage movement, reservation booking/cancel/no-show, selling payment totals, and
easy/pro dashboard summaries.
It now also includes production-core control examples for RBAC, validation,
audit events, inventory availability, and paid-stock fulfillment.
The latest slice adds tenant/session checks, idempotent ledger entry rules,
account balance math, and recovery checks.
Security/ops evidence now includes a tamper-evident audit chain, secret
redaction, health checks, and restore parity.
Persistence boundary evidence includes schema versioning, migration status,
repository snapshots, and restore/snapshot parity.
Guarded write evidence now proves CRM, reservation, and sale write attempts
pass through session, RBAC, validation, audit, and ledger/idempotency gates.
Write requests also produce decisions and receipts so accepted/denied outcomes
are explicit.
Readiness evidence aggregates identity, RBAC, validation, ledger, recovery,
security, and guarded-write gates for release handoff.
Durable-store readiness is intentionally blocked until the example has a
supported durable storage facade.

## Unified Business Suite (UBS) Integration

Core MDSOC modules now integrated:
- **Kernel**: event_log, projection, commit_loop — append-only ledger + balanced-entry invariant
- **Dimensions**: money (nominal, no coercion), time, location, identity, approval, permission
- **Tests**: event_log_spec, projection_spec, commit_loop_spec, dimensions_spec, money_spec

See `doc/unified_business_suite_mdsoc.md` for full MDSOC architecture and feature catalog.

## Business Suite framework

Shared guarded-write framework (`src/framework/guarded.spl`) unifies all lane writes with closed reasons: accepted, invalid-session, forbidden, invalid-record, duplicate-key, needs-approval. Five lanes (crm, reservation, sale, market, restaurant) in `src/lanes/` inherit all framework gates.

Web routing via `src/web/routes.spl` maps HTTP method+path to lane actions with read/write RBAC distinction. Accounting posting bridge (`src/kernel/posting.spl`) posts balanced journal entries for accepted writes to the event-sourced kernel ledger.

Reporting module (`src/report/summary.spl`) derives per-lane accepted/denied/revenue KPIs and totals. HTML dashboard generator (`src/web/dashboard.spl`, entry `src/dashboard_main.spl`) renders self-contained output (inline CSS, no external assets, HTML-escaped values) with KPI tiles and per-lane status cards.

The framework is extensible by registration (`src/framework/registry.spl`): a
new business is one `LaneDef` + one lane module — RBAC, routes, gating, and
dashboard cards derive from the registry (proof: `src/extension_demo.spl`,
clinic lane, zero framework edits). Role policy and ordered approval chains are
registry data too (`src/framework/org.spl`). Big-business mechanics — durable
event log with fail-closed load (`src/kernel/durable_log.spl`), materialized
balance snapshots, bucketed idempotency index, per-tenant FIFO commit queue —
are proven end-to-end by `src/bigbiz_demo.spl`.

See `doc/01_research/domain/simple_erp_vs_sap.md` for comparison research,
`doc/05_design/simple_erp_extension.md` for the extension design, and
`doc/07_guide/app/simple_erp/business_framework.md` for the how-to guide.

Run:

```bash
bin/simple test test/03_system/app/simple_erp/feature/ --mode=interpreter      # all 4 system specs
bin/simple examples/12_business/simple_erp/src/catalog.spl easy
bin/simple examples/12_business/simple_erp/src/catalog.spl pro
bin/simple test examples/12_business/simple_erp/ubs_test/ --mode=interpreter   # kernel + lane + report specs
bin/simple examples/12_business/simple_erp/src/business_suite.spl              # suite evidence
bin/simple examples/12_business/simple_erp/src/dashboard_main.spl              # HTML dashboard to stdout
bin/simple examples/12_business/simple_erp/src/extension_demo.spl              # 6th business, zero framework edits
bin/simple examples/12_business/simple_erp/src/bigbiz_demo.spl                 # durability/snapshot/queue/org evidence
```
