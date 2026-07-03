# Simple ERP Suite vs SAP ERP/CRM and Peer Business Apps

Honest scope: SAP S/4HANA + SAP CRM (C4C/Sales Cloud) are enterprise products
with decades of localization, compliance, and module depth. This suite targets
the **small-business slice** (CRM + reservation + sale + market + restaurant).
The comparison below is per-dimension: where we already match or beat the
incumbents *at this scope*, and which gaps we close vs. defer.

## Feature comparison (small-business scope)

| Dimension | SAP S/4 + CRM | Odoo / ERPNext | This suite (before) | This suite (after this pass) |
|---|---|---|---|---|
| Write governance | authorizations + workflow | per-model ACL | ONE guarded gate, closed reasons, all 5 lanes | same (already stronger: 4 denial reasons spec-pinned per lane) |
| Accounting core | FI/CO, universal journal | double-entry ledger | UBS kernel ledger existed but **unwired** | accepted writes post **balanced journal entries** to event-sourced ledger |
| Approval workflow | release strategies | approval rules | dimension existed, unwired | threshold+role approval wired into the gate (`needs-approval` reason) |
| Audit | change documents | chattel logging | tamper-evident chain + event log | same, ledger drill-down from balance to event |
| Reporting | embedded analytics/BW | dashboards | text dashboards only | per-lane KPI report + financial summary from ledger projection |
| Look/UI | Fiori | web UI | none (CLI text) | generated HTML dashboard (KPI tiles, per-lane cards), pure Simple |
| CRM pipeline | Sales Cloud stages | kanban CRM | stages, quotes, next actions | same + approval threshold on high-value writes |
| POS/restaurant | add-on partners | Odoo POS | menu/table/kitchen/split/tips | same |
| Marketplace | Commerce (separate) | website/store | listings/orders/commission/payout | same |
| Multi-tenant identity | complex | multi-company | tenant+session fail-closed in gate | same |

## Where this suite is genuinely better (by construction, at its scope)

- **No sync errors possible**: financial views are projections of ONE event
  log; SAP-class systems reconcile between modules — we have nothing to reconcile.
- **Fail-closed writes, spec-pinned**: every lane has all four denial reasons
  asserted in executable specs; the gate is one function, not policy spread
  across modules.
- **Auditability**: balance → journal entry → event is one chain; tamper-evident
  audit hash; secret redaction tested.
- **Footprint**: zero-dependency single binary + .spl sources vs. NetWeaver/HANA stack.

## Where SAP (and Odoo/ERPNext) remain ahead — deferred, not hidden

- Localization/compliance (tax regimes, e-invoicing, GAAP/IFRS close), HR,
  manufacturing (MRP), warehouse logistics, BW-scale analytics, ecosystem/ISVs.
- Live durable store (simple_db integration is the known blocker), live
  identity/secret backends, deployed backup service.
- Concurrency/scale hardening beyond in-memory example scope.

## Gap-closing work in this pass

1. **Accounting integration** — `post_accepted_write` builds a balanced
   JournalEntry (cash/revenue or deposit lines) per accepted lane write and
   appends it to the UBS kernel event log; projection proves balances.
2. **Approval workflow** — `gate_write_with_approval` extends the gate:
   amounts at/over the lane threshold require the approver role, else
   `needs-approval` (closed reason set grows by one, spec-pinned).
3. **Reporting** — `src/report/summary.spl` derives per-lane KPIs +
   ledger-backed financial totals.
4. **Look** — `src/web/dashboard.spl` renders a self-contained HTML dashboard
   (KPI tiles, lane cards, status colors) written in pure Simple; system test
   asserts on the generated markup.
