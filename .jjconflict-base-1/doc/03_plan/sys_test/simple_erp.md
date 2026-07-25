# Simple ERP System Test Plan

Run:

```bash
bin/simple test test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl --mode=interpreter
```

Submodule evidence:

```bash
git submodule status examples/12_business/simple_erp
```

Checks:

- easy mode exists
- pro mode exists
- CRM, reservation, and selling lanes exist
- easy mode summarizes open leads, open reservation slots, and unpaid sales
- pro mode exposes numeric CRM, reservation, and selling totals
- the SPipe spec runs the Simple ERP script and checks stdout from real code
- the SPipe spec checks `easy` and `pro` CLI mode selection
- the Simple script has assertions for lead advancement, quote approval,
  reservation booking, hold/deposit, cancellation, no-show, payment state,
  payment audit count, and selling channel count
- the Simple script has assertions for RBAC, validation, audit events,
  inventory availability, and paid-stock fulfillment
- the Simple script has assertions for tenant/session validity, ledger
  idempotency, ledger totals/account balance, and recovery readiness
- the Simple script has assertions for audit-chain tamper detection, session
  secret redaction, operational health, and restore parity
- the Simple script has assertions for schema migration status, repository
  snapshots, and restore/snapshot parity
- the Simple script has assertions for guarded CRM, reservation, and sale write
  acceptance and denial counts
- the Simple script has assertions for write decisions and accepted receipts
- the Simple script has assertions for aggregate production readiness gates
- the Simple script has assertions that durable-store readiness is missing and
  blocks production readiness
