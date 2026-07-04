# Domain Research: Simple ERP

ERP products commonly group business work around CRM, sales, inventory,
accounting, ecommerce/POS, appointments/reservations, and reporting. ERPNext and
Odoo both expose broad module catalogs that combine CRM, selling, stock,
appointments/POS/ecommerce, and back-office controls.

For this example, the smallest useful domain slice is a feature catalog that
keeps small-business easy flows separate from professional audit/detail flows.

## Feature-Needs Matrix by Product Area

| Area | Must-Have | Nice-to-Have | Local Coverage | Gap |
|------|-----------|--------------|-----------------|-----|
| **ERP Core** | Accounts & ledger, multi-tenant RBAC, session mgmt, audit trail, validation gates | Budget tracking, cost allocation, multi-currency | REQ-017,025,026; src/lib/*/ledger, web_framework auth; catalog.spl audit chain + restore parity (REQ-018,019) | Approval workflows, durable backup/restore service |
| **CRM** | Leads, accounts/contacts, pipeline stages, quotes, activities/next-actions | Segment scoring, funnel analytics, bulk actions | REQ-002,007,023; examples/12_business/simple_erp lane | Territory mgmt, forecast, email sync |
| **Market** | Listings, orders, payments, seller payouts, stock depletion, commission math | Bulk listing tools, rating/review, recommendation | Partial; payment lib exists (src/lib/nogc_async_mut/payment) | Market lane module (REQ-029), order→stock sync, payout ledger |
| **Restaurant** | Menu items, table orders, kitchen routing, bills with split/tips, reservations, no-show tracking | Loyalty, delivery zone mgmt, prep time estimates, mobile order | Partial; examples/06_io/restaurant_webapp has menu/order/payment; REQ-003,008,009 | Forward-only state machine (REQ-030), bill split math, full kitchen workflow |

## Architecture Alignment

All five lanes run on a shared guarded-write framework (REQ-027) deployed in examples/12_business/simple_erp atop a durable store candidate (examples/11_advanced/simple_db). Each lane module (CRM, reservation, sale, market, restaurant) inherits session→RBAC→validation→idempotency gates, with a web route table (REQ-031) mapping HTTP method+path to lane actions and read/write RBAC. Acceptance/denial evidence flows through a suite entrypoint (REQ-032) with per-lane counters and sspec unit/system coverage (REQ-033,034).
