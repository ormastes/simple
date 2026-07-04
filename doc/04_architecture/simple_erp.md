<!-- codex-architecture -->
# Simple ERP Architecture

`examples/12_business/simple_erp` is a local example submodule. Its
`src/catalog.spl` is a single-file, in-memory ERP seed with three business lanes
and two operator views. Keep it that way until a real persistence or routing
need appears.

Submodule-local architecture companion: `examples/12_business/simple_erp/doc/architecture.md`.

## Structure

- Feature catalog: lane ids plus easy/pro descriptions for CRM, reservation,
  and selling.
- CRM slice: leads with account, contact, stage, value, next action, and quote
  approval visibility.
- Reservation slice: resource, kind, capacity, booked count, and remaining
  slots, plus hold/cancel/no-show state.
- Selling slice: channel, subtotal, tax, payment state, audit note, and unpaid
  total.
- Easy mode: daily operator summary built from the same business facts.
- Pro mode: numeric control summary for managers and accounting.
- CLI selector: `easy`, `pro`, or default combined output.
- Production core: RBAC, validation, audit events, inventory availability, and
  paid-stock fulfillment checks.
- Recovery core: tenant/session checks, idempotent ledger entries, account
  balances, and restore-readiness checks.
- Security/ops core: tamper-evident audit-chain evidence, secret redaction,
  health checks, and restore parity.
- Persistence core: schema migration status, repository snapshots, and
  restore/snapshot parity.
- Write core: guarded CRM, reservation, and sale write facade over session,
  RBAC, validation, audit, and ledger/idempotency gates.
- Readiness core: aggregate identity, RBAC, validation, ledger, recovery,
  security, and write-gate status for release handoff evidence.
- Durability core: explicit durable-store readiness gate. It currently fails
  closed because this example has no supported durable store facade.

## Data Flow

- The catalog defines the feature surface.
- Sample CRM, reservation, and sale lists feed the dashboard helpers.
- `lead_pipeline_value`, `approved_quote_total`, `open_reservation_slots`,
  `unpaid_sales_total`, and `payment_audit_count` compute shared metrics once.
- `easy_mode_dashboard` and `pro_mode_dashboard` format the same results for
  different users.
- `render_interface` chooses which view the command prints without changing the
  underlying workflow state.

## Boundaries

- The submodule currently uses a local `.gitmodules` URL because the expected
  `ormastes/simple-erp` GitHub repository does not exist.
- Production roadmap and agent-team ownership live in
  `examples/12_business/simple_erp/doc/production_plan.md` and
  `examples/12_business/simple_erp/doc/agent_teams.md`.
- Recovery plan lives in
  `examples/12_business/simple_erp/doc/recovery_plan.md`.
- Stay in-memory for this example; do not introduce persistence or services.
- Reuse restaurant-specific ordering behavior from
  `examples/06_io/restaurant_webapp` if the selling lane grows into a web
  ordering flow.
- Reuse `src/lib/nogc_async_mut/payment` for payment rules instead of inventing
  another payment model.
- Follow `examples/11_advanced/simple_db` patterns if the example is later
  promoted to stored state.

## Design Notes

- No MDSOC capsule is needed yet: the example is still one small catalog plus
  pure helpers.
- If the file splits, move shared feature metadata upward first, then keep mode
  formatting and domain math separate.
- Hot-path work is trivial: the two dashboards should only walk the sample
  lists once and should not duplicate formulas in presentation code.
