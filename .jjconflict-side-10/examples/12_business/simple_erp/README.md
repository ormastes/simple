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

Run:

```bash
bin/simple test test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl --mode=interpreter
bin/simple examples/12_business/simple_erp/src/catalog.spl easy
bin/simple examples/12_business/simple_erp/src/catalog.spl pro
```
