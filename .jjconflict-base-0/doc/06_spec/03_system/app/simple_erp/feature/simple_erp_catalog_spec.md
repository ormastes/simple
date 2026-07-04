# Simple ERP Catalog Spec

The Simple ERP example exposes a feature catalog with easy and pro mode coverage.

## Acceptance

- The summary names easy mode.
- The summary names pro mode.
- The catalog has CRM, reservation, and selling lanes.
- Easy mode shows open leads, open reservation slots, and unpaid sales.
- Pro mode shows pipeline value, approved quote value, open reservation slot
  count, unpaid sales total, five selling channels, and five payment audits.
- Production controls show RBAC roles, CRM/reservation/sale validation, audit
  evidence, inventory availability, and paid-stock fulfillment.
- Production recovery shows tenant/session evidence, ledger entry count, ledger
  total, idempotency status, and recovery check count.
- Production security shows audit chain validity, secret redaction, operational
  health, and restore parity.
- Production persistence shows schema version, migration status, snapshot
  consistency, and restore/snapshot parity.
- Production writes show guarded CRM/reservation/sale write acceptance and
  denial through session, RBAC, validation, audit, and ledger gates.
- Production writes show accepted receipt count.
- Production durability shows the durable-store blocker.
- Production readiness shows aggregate gate pass count and blocks production
  readiness while durable storage is missing.
- `easy` mode prints only the easy operator view.
- `pro` mode prints only the professional numeric view.
- The executable spec runs `examples/12_business/simple_erp/src/catalog.spl`
  through `bin/release/x86_64-unknown-linux-gnu/simple`, so the assertions cover
  the implementation script.

Executable spec: `test/03_system/app/simple_erp/feature/simple_erp_catalog_spec.spl`

Submodule path: `examples/12_business/simple_erp`
