# Simple ERP Feature Requirements

- REQ-001: The example shall expose an easy mode and pro mode concept.
- REQ-002: The example shall include a CRM lane.
- REQ-003: The example shall include reservation infrastructure for meeting,
  hotel room, and restaurant-style resources.
- REQ-004: The example shall include selling infrastructure for online shop,
  unmanned shop, restaurant, coffee/meal/bakery, auction, and retail shop lanes.
- REQ-005: Easy mode shall show a daily action summary for open leads, open
  reservation slots, and unpaid selling work.
- REQ-006: Pro mode shall show numeric operational totals for CRM pipeline,
  reservation capacity, and unpaid sales.
- REQ-007: CRM shall support account/contact lead ownership, quote approval
  totals, and moving a lead to a new stage with a next action.
- REQ-008: Reservation shall reject over-capacity booking and support booking,
  holds with deposit, cancellation, and no-show state.
- REQ-009: Selling shall support paid/unpaid order state and totals across online
  shop, unmanned shop, restaurant coffee/meal/bakery, auction, and retail shop.
- REQ-010: Pro mode shall expose payment audit visibility for every sample
  selling channel.
- REQ-011: The example CLI shall support `easy` and `pro` mode arguments and a
  combined default output.
- REQ-012: The production core shall expose RBAC role checks for admin,
  operator, and auditor users.
- REQ-013: The production core shall validate CRM, reservation, and sale records
  before workflow use.
- REQ-014: The production core shall expose audit event evidence for controlled
  actions.
- REQ-015: The production core shall expose inventory availability and paid
  order fulfillment checks for store workflows.
- REQ-016: The production core shall expose tenant/session validation.
- REQ-017: The production core shall expose idempotent append-only ledger entry
  checks and account balance math.
- REQ-018: The production core shall expose backup/restore recovery readiness
  checks.
- REQ-019: The production core shall expose tamper-evident audit chain checks.
- REQ-020: The production core shall redact session secrets from operator
  output.
- REQ-021: The production core shall expose operational health and restore
  parity checks.
- REQ-022: The production core shall expose schema migration status, repository
  snapshots, and restore/snapshot parity.
- REQ-023: CRM, reservation, and sale write attempts shall pass tenant/session,
  RBAC, validation, audit, and ledger/idempotency gates before acceptance.
- REQ-024: Guarded writes shall emit explicit decisions and receipts for
  accepted and denied outcomes.
- REQ-025: The production core shall expose an aggregate readiness gate covering
  identity, RBAC, validation, ledger, recovery, security, and guarded writes.
- REQ-026: The production core shall expose durable-store readiness separately
  and block production readiness when no durable store is available.
