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
| Accounting core | FI/CO, universal journal | double-entry ledger | UBS kernel ledger existed but **unwired** | posting bridge (events + balanced journal entries), exercised by the suite with demo amounts |
| Approval workflow | release strategies | approval rules | dimension existed, unwired | `gate_write_with_approval` overlay (`needs-approval`), thresholds registered per LaneDef |
| Audit | change documents | chattel logging | tamper-evident chain + event log | same, ledger drill-down from balance to event |
| Reporting | embedded analytics/BW | dashboards | text dashboards only | per-lane KPI report + totals (ledger balances proven separately by projection specs) |
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

- Live deployment concerns (HA/DR, monitoring, upgrades) and the
  compliance/localization content moat (tax regimes, e-invoicing, GAAP/IFRS
  close, HR, MRP, warehouse logistics, BW-scale analytics, ecosystem/ISVs)
  remain SAP territory.

## Gap-closing work in this pass

1. **Accounting integration** — `kernel/posting.spl` provides the bridge:
   `post_accepted_write` appends an accounting event per accepted write and
   `journal_for_accepted` builds the balanced cash/revenue JournalEntry;
   projection proves balances. The suite demonstrates the flow with demo
   amounts; lanes do not yet auto-post (durable-store wiring is the tracked
   next step).
2. **Approval workflow** — `gate_write_with_approval` overlays the gate:
   amounts at/over a threshold require the approver role, else
   `needs-approval` (closed reason set grows by one, spec-pinned). Thresholds
   are LaneDef registration data.
3. **Reporting** — `src/report/summary.spl` derives per-lane KPIs +
   ledger-backed financial totals.
4. **Look** — `src/web/dashboard.spl` renders a self-contained HTML dashboard
   (KPI tiles, lane cards, status colors) written in pure Simple; system test
   asserts on the generated markup.

## Big-business mechanics closed in the follow-up pass

| Aspect | Implementation |
|--------|---|
| Durability | file-persisted event log, checksum, fail-closed load — REQ-039 |
| Volume | materialized balance snapshots + bucketed key index — REQ-040/041 |
| Concurrency | per-tenant FIFO commit queue, atomic drain, single-writer property — REQ-042 |
| Org complexity | roles + ordered approval chains as registry data — REQ-043 |
| Proof | bigbiz_demo.spl entrypoint + simple_erp_bigbiz_spec.spl system test |

These are example-scope mechanics proving the architecture, not a deployed HA cluster.
