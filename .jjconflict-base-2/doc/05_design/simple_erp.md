<!-- codex-design -->
# Simple ERP Detail Design

Implementation lives in the local example submodule
`examples/12_business/simple_erp`.

Submodule-local design companion: `examples/12_business/simple_erp/doc/design.md`.
Production plan: `examples/12_business/simple_erp/doc/production_plan.md`.
Agent teams: `examples/12_business/simple_erp/doc/agent_teams.md`.
Recovery plan: `examples/12_business/simple_erp/doc/recovery_plan.md`.

## Data Model

- `ErpFeature`: lane id plus easy/pro descriptions.
- `CrmLead`: customer name, account, contact, stage, expected value, and next
  action.
- `CrmQuote`: lead id, amount, and approval state.
- `Reservation`: resource name, resource kind, capacity, booked count, status,
  and deposit.
- `Sale`: sales channel, subtotal, tax, payment state, status, and audit note.

## Business Rules

- `erp_features()` returns exactly three lanes: CRM, reservation, and selling.
- `erp_has_lane(name)` is a simple membership check for lane registration.
- `lead_pipeline_value(leads)` sums only open CRM value and skips won deals.
- `advance_lead(lead, stage, next_action)` records stage movement and next work.
- `approved_quote_total(quotes)` sums approved quotes for pro mode.
- `reservation_can_book(reservation, seats)` rejects zero/negative seats and
  any booking that would exceed capacity.
- `book_reservation`, `hold_reservation`, `cancel_reservation`, and
  `no_show_reservation` model the requested reservation lifecycle.
- `open_reservation_slots(reservations)` totals remaining capacity across all
  active resources.
- `sale_total(sale)` and `unpaid_sales_total(sales)` compute gross totals and
  outstanding revenue.
- `mark_sale_paid(sale)` and `payment_audit_count(sales)` model payment
  completion and audit visibility.
- `easy_mode_dashboard()` produces a daily operator sentence.
- `pro_mode_dashboard()` produces a numeric control sentence.
- `render_interface(mode)` selects `easy`, `pro`, or the combined default view.
- `role_can`/`user_can` enforce the first admin/operator/auditor permission
  surface.
- `validate_lead`, `validate_reservation`, and `validate_sale` guard sample
  domain records.
- `audit` creates controlled-action evidence.
- `inventory_available`, `order_can_fulfill`, and
  `fulfillable_order_count` cover basic store stock safety.
- `session_valid`, `ledger_accepts_new`, `ledger_account_balance`, and
  `recovery_ready` cover the first tenant/session/ledger/recovery controls.
- `audit_chain_valid`, `safe_session_label`, `operations_ready`, and
  `production_security_summary` cover tamper evidence, secret redaction, health,
  and restore parity.
- `snapshot_current`, `migrations_current`, `restore_matches_snapshot`, and
  `production_persistence_summary` cover schema migration and snapshot parity.
- `guarded_crm_write`, `guarded_reservation_write`, `guarded_sale_write`, and
  `production_write_summary` cover guarded production writes.
- `decide_write_request`, `write_receipt`, and `accepted_receipt_count` cover
  explicit result reporting.
- `sample_readiness_gates`, `production_ready`, and
  `production_readiness_summary` cover aggregate release-gate evidence.
- `sample_durable_snapshot`, `durable_snapshot_ready`, and
  `production_durability_summary` expose the durable-store blocker without
  calling runtime file/process APIs from business logic.

## Example Coverage

- CRM sample: three leads, with one won lead excluded from pipeline value.
- Quote sample: one approved quote contributes 250000 to pro totals.
- Reservation sample: meeting room, hotel room, and restaurant-style resource.
- Selling sample: online shop, unmanned shop, restaurant bundle, auction, and
  retail shop.
- The sample outputs are stable enough to support docs and smoke checks without
  extra scaffolding.

## Acceptance Notes

- Easy mode should surface open leads, open slots, and unpaid sales in one
  short summary.
- Pro mode should surface pipeline value, approved quote value, reservation
  availability, unpaid revenue, selling channel count, and payment audit count.
- CLI mode selection should print only the easy view for `easy`, only the pro
  view for `pro`, and both views by default.
- Reservation guard should accept four seats in a ten-seat room with six seats
  booked, and reject five.
- Reservation lifecycle should cover book, hold with deposit, cancel, and
  no-show.
- Selling lifecycle should cover unpaid totals and paid state transition.

## Six-Hour Build Plan

1. Hour 1: finalize catalog data, requirements, architecture, and example
   assertions.
2. Hour 2: flesh out CRM records, stage labels, and pipeline math.
3. Hour 3: flesh out reservation records, availability, and overbooking guard.
4. Hour 4: flesh out selling records, channel totals, and unpaid total math.
5. Hour 5: wire easy and pro summaries onto the same underlying facts.
6. Hour 6: trim duplication, review docs, and finish the example smoke path.
