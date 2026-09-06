# Simple Enterprise Suite — Assessment, Design, and Parallel-Agent Plan (2026-08-16)

## Executive verdict

The repository does not yet contain a full enterprise solution. It contains a tested and well-structured business-framework prototype that is useful as the seed of a larger product.

The existing implementation already demonstrates:

- a common guarded-write path;
- tenant/session checks and role-based authorization;
- validation and idempotency;
- approval decisions;
- event, projection, posting, snapshot, and recovery concepts;
- small CRM, sales, reservation, marketplace, and restaurant domains;
- interpreter-mode specifications;
- a static HTML dashboard.

However, both the monorepo example and the standalone ormastes/simple-erp repository explicitly describe themselves as in-memory implementations, and their readiness documentation blocks production use until durable storage, live identity/secrets, automated recovery, monitoring, migration, and deployment controls exist.

Scope-weighted estimate:

> Approximately 8–12% of the requested executable enterprise product exists.

This is a heuristic estimate of product capability, not LOC coverage. Architecture documentation is considerably further ahead than integrated functionality.

---

## 1. Current implementation assessment

### 1.1 Maturity matrix

Scale: 0 absent · 1 isolated model or helper · 2 tested prototype · 3 integrated durable MVP · 4 pilot-ready · 5 enterprise production

| Area | Current state | Level |
|---|---|---|
| Enterprise capability architecture | Broad UBS/MDSOC+ enterprise blueprint | 2 |
| Shared guarded-write framework | Session → RBAC → validation → idempotency, approval overlay | 2 |
| Event, projection, posting kernel | Tested architectural examples | 2 |
| CRM | One lead record and pipeline-stage movement | 1 |
| Sales | Subtotal, tax, payment flag, and status helpers | 1 |
| Inventory | Small availability and fulfillment examples | 1 |
| Reservation | Capacity, hold, cancel, and no-show helpers | 1 |
| Rental | No complete rental lifecycle | 0 |
| Restaurant | Minimal menu item and table-order state machine | 1 |
| Marketplace | Listing, stock, commission, and payout calculations | 1 |
| Accounting | Balanced posting concepts, but no operational general ledger | 1 |
| Procurement | No integrated requisition-to-payment flow | 0 |
| HR/HCM/payroll | No product implementation | 0 |
| Employee/admin UI | Static KPI dashboard only | 1 |
| Customer/POS/table/KDS UI | Not implemented | 0 |
| Live application API | Pure route simulation; no integrated application server | 0 |
| Production database | Explicitly blocked | 0 |
| Recovery and operations | Helpers and documentation, not deployed automation | 1 |
| Production security assurance | Selected controls and unit specs only | 1 |

The domain files confirm that CRM is currently a Lead, reservations are a capacity counter, sales are basic totals/status, marketplace support is a local listing/order calculation, and restaurant support is a small forward-only order state machine.

There is meaningful testing around the kernel, domains, routing, approval, reporting, snapshots, durable log, commit queue, and organization rules. These tests currently operate mainly through the interpreter and pure function interfaces rather than a live browser → server → database system.

### 1.2 What should be preserved

1. The common guarded-write rule. Domain modules cannot independently bypass session, authorization, validation, or idempotency checks.
2. Registry-driven domain extension.
3. Explicit accepted/denied results.
4. Approval as a shared concern.
5. Immutable posting and event concepts.
6. Interpreter specifications as executable design evidence.
7. MDSOC+ module ownership and restricted visibility.

The current durable_log.spl should not become the production ledger. Its source explicitly describes its checksum as a toy, non-cryptographic digest; it also writes a complete line-oriented file rather than participating in an ACID database transaction. It remains useful for fixtures, export, and recovery experiments.

---

## 2. Repository and product boundary

**ormastes/simple** owns: Simple language and compiler; runtime; standard libraries; web-server framework; database adapters; UI framework; OS and hardware support; common testing and documentation infrastructure. It should retain only a small enterprise compatibility example and smoke tests.

**ormastes/simple-erp, renamed or evolved into simple-enterprise** owns: the enterprise product; database schema and migrations; business modules; web/POS/table/KDS applications; deployment configuration; integration adapters; operational runbooks; country packs.

The standalone repository currently contains substantially the same prototype sources as the monorepo example and still identifies itself as an in-memory implementation. It is nevertheless the correct product boundary because enterprise releases should not be coupled to unrelated compiler, OS, RISC-V, browser, and rendering changes.

Working name: **Simple Enterprise Suite**, internally organized using the existing Unified Business Suite / MDSOC+ architecture.

---

## 3. Web-server robustness assessment

The server infrastructure is more advanced than the ERP application. The asynchronous server includes worker event loops, SO_REUSEPORT, incremental HTTP parsing, HTTP/2 structures, TLS/ALPN, compression, static files, range responses, middleware, and graceful draining.

It is still not ready to be the directly exposed public edge of a payment- and identity-bearing enterprise product.

### 3.1 Critical issue: sync/async security divergence

Recent hardening was explicitly applied to nogc_sync_mut/http_server: request limits, path-safety checks, duplicate Content-Length rejection, and fail-closed behavior for unsupported chunking. The async server has a separate parser and router and therefore does not automatically inherit those controls. The hardening record also notes unresolved end-to-end bounded-read evidence and some pre-existing security-test import failures.

This duplication should be removed:

```
http_core/
  parser.spl
  request_limits.spl
  header_validation.spl
  path_normalization.spl
  routing.spl
  response.spl
  security_policy.spl

http_transport/
  sync/
  async/
```

Both transports must consume the same protocol core and run the same conformance, fuzz, and request-smuggling corpus.

### 3.2 Release-blocking async-server findings

**Request limits are applied too late.** The async parser grows its buffer and materializes the request body, while the middleware body-size check runs after request parsing. That does not reliably prevent memory exhaustion by a declared or streamed oversized body. The reviewed async parser also does not visibly enforce the sync implementation's request-line, header-count, and per-header limits.

Limits must be enforced during parsing, before buffer growth: request-line bytes; total header bytes; header count; individual header bytes; declared body bytes; decoded chunk bytes; multipart field and file bytes; route-specific upload limits.

**Static-path confinement is not shared.** The reviewed async worker constructs static paths from root + request.path, and the async router does not invoke the sync router's path_is_safe guard.

Required behavior:
1. Decode according to one canonical policy.
2. Reject NUL, backslash, encoded separators, double encoding, and traversal.
3. Canonicalize the final path.
4. Verify that it remains beneath the configured root.
5. Prefer descriptor-relative open APIs where available.
6. Initially serve static files at the edge proxy rather than the application process.

**Dynamic handler dispatch needs a live proof.** In the reviewed request path, a successful route match appears to invoke the inline static handler directly, despite separate handler-registry and security-context dispatch functions being present. This may be incomplete wiring rather than intended behavior. A live system test must prove that API routes call the requested dynamic handler under a server-established security context.

**Native runtime correctness is a production blocker.** The async worker contains repeated workarounds stating that Dict.get() can return corrupted class or struct payloads in native code generation. The latest repository note also records that focused checks using the deployed pure-Simple executable terminate with signal 11, exit code 139.

An enterprise product cannot admit a runtime with known container-materialization corruption. This needs: minimized compiler/runtime regression cases; sanitizer-enabled native builds where supported; interpreter/native differential tests; forced admission gates for arrays, dictionaries, optionals, results, rows, and nested business aggregates; removal of workaround-only acceptance criteria once the defect is fixed.

**Direct public TLS/HTTP/2 should be deferred.** The reviewed worker performs TLS handshake work synchronously in the accept flow, allowing a slow handshake to occupy a worker. HTTP/2 also needs strict preface, HPACK, stream, frame, memory, and concurrency limits.

Initial deployment topology:

```
Internet
   |
CDN / WAF / mature reverse proxy
  - TLS
  - HTTP/2 and HTTP/3
  - request limits
  - static files
  - coarse rate limiting
   |
private HTTP/1.1 or Unix socket
   |
Simple enterprise application
```

Direct Simple TLS/H2 exposure becomes a later platform milestone, not a prerequisite for the enterprise package.

### 3.3 Web-server admission gate

The server becomes eligible for direct enterprise use only when:

- sync and async use one parser/router/security core;
- all limits are enforced before allocation;
- path confinement is end-to-end tested;
- dynamic route dispatch is proven;
- native corruption defects are closed;
- slow-header, slow-body, partial-I/O, and pending-write limits pass;
- parser, path, multipart, range, TLS, HTTP/2, and proxy fuzzing passes;
- request-smuggling differential tests against the selected proxy pass;
- ASVS and API authorization controls have traceable test evidence.

OWASP positions ASVS 5.0.0 as the current stable, verifiable application-security standard. API-specific testing must additionally cover object- and function-level authorization, resource exhaustion, sensitive-business-flow automation, SSRF, API inventory, and unsafe consumption of third-party APIs.

---

## 4. Database decision

### 4.1 Do not make Simple DB the enterprise dependency yet

The current repository documentation says:

- the operational tier is an embedded SDN/file database;
- the historical full MVCC/WAL implementation is an unfinished skeleton and is absent from the current worktree;
- the SimpleOS database service is a small bounded store, not a general database server;
- PostgreSQL/libSQL drivers, pooling, transactions, mapping, and introspection remain planned work.

The current performance report also records: server mode unavailable; unsafe native row/scalar materialization; corrupted query-result lengths; a focused native probe terminating with exit 139; current timings not being acceptable as correctness evidence.

Therefore:

> Finance, payroll, customer PII, payment state, booking truth, and inventory truth must not use Simple DB in the first production package.

Keep Simple DB as a separate research and compatibility track.

### 4.2 Use PostgreSQL as the system of record

Recommended first-production topology:

```
Application instances
       |
connection pool
       |
PostgreSQL primary
  |         |
standby   WAL archive
  |         |
failover  point-in-time recovery
```

PostgreSQL provides database-enforced row-security policies, WAL-based point-in-time recovery, standby operation, and range exclusion constraints that can prevent overlapping reservations at the database level.

Core rules:

- one PostgreSQL cluster and modular schemas initially;
- every tenant-owned table includes tenant_id;
- application roles do not own tables or have BYPASSRLS;
- use FORCE ROW LEVEL SECURITY where appropriate;
- tenant context is set by the authenticated server, never trusted from request JSON;
- business commands and outbox rows commit in one transaction;
- idempotency keys are unique database constraints;
- financial and stock postings are append-only;
- exclusive bookings use range exclusion constraints or equivalent serializable locking;
- use expand → backfill → contract migrations;
- restore and reconciliation tests are release gates.

### 4.3 SQLite is suitable for bounded offline edge use

A real SQLite runtime binding and Simple wrapper already support open/close, prepared statements, typed binds, queries, and transaction calls.

Use it for: offline retail POS commands; restaurant table-tablet pending orders; local KDS continuity; demos and developer mode.

Before admission, add: migration/version tables; WAL and busy-timeout configuration; enforced foreign keys; prepared-statement-only repositories; typed row mapping; encrypted token storage; power-loss, disk-full, and corruption tests; a bounded local operation journal; idempotent server replay; cursor and reconciliation logic; reset and re-provision procedures.

SQLite must remain a cache and pending-command store, not the enterprise source of truth.

---

## 5. Target architecture

Use a modular monolith first, because the critical workflows require atomic transactions across several domains.

```
Customer Web/PWA      POS/Kiosk      Table Tablet      Employee/Admin
        \                 |                |                 /
                    Edge proxy
                         |
               Simple application
  +------------------------------------------------------+
  | Foundation | CRM | Sales | Catalog | Inventory       |
  | Procurement | Finance | Booking/Rental | Restaurant  |
  | HCM | Support | Channel Hub | Analytics              |
  +------------------------------------------------------+
                         |
                 PostgreSQL + outbox
                         |
       +-----------------+-------------------+
       |                 |                   |
 connector workers  notification jobs  device gateway
       |                                     |
 Amazon/others                     table tablets/KDS/POS
```

Extract separate processes only for: marketplace connectors; notifications; document/media processing; analytics/search; restaurant/POS device gateway.

Do not begin with microservices for sales, inventory, payment, booking, and finance. Their invariants are easier to preserve inside one transactional process.

### 5.1 Shared enterprise foundation

Freeze and implement these before individual modules grow:

- tenant, legal entity, business unit, location, cost center;
- party, person, organization, customer, supplier, employee linkage;
- identity, actor, session, service account, device identity;
- money, currency, quantity, unit, tax class, time range;
- typed IDs and optimistic aggregate versions;
- permission and policy decisions;
- approval, delegation, segregation of duties;
- document numbering and status transitions;
- audit records;
- idempotency;
- repository, unit of work, transaction, migration, outbox;
- localization, retention, privacy request, notification, attachment.

---

## 6. Enterprise package modules

| Package | Required scope |
|---|---|
| Foundation | Tenants, companies, locations, users, devices, roles, approvals, audit, workflow |
| Party and CRM | Leads, accounts, contacts, activities, opportunities, quotes, contracts |
| Sales | Cart, quotation, order, fulfillment, invoice request, return, customer credit |
| Catalog and pricing | Product, variant, SKU, barcode, bundle, menu link, price lists, tax, promotions |
| Inventory/WMS | Warehouses, bins, lots/serials, stock ledger, reservation, transfer, picking, count |
| Procurement | Requisition, RFQ, supplier quote, PO, receipt, purchase invoice, replenishment |
| Finance | Chart of accounts, journals, AR/AP, tax, payment allocation, reconciliation, close |
| Booking | Time-ranged resources, capacity pools, assigned seats, waitlists, holds |
| Rental | Rate plans, deposits, check-in/out, extension, damage, fines, maintenance |
| Restaurant | Reservation, floor/table, table session, menu/modifiers, kitchen tickets, bills |
| HCM | Employee, position, contract, attendance, shift, leave, expense, onboarding |
| Payroll boundary | Effective-dated inputs, calculation evidence, payslip, accounting export |
| Channel Hub | Amazon and other store adapters, mappings, notifications, reconciliation |
| Support/projects | Cases, SLA, projects, tasks, time, expenses |
| Analytics | Operational reporting, finance reports, warehouse export, governed AI assistance |

For the Korean country pack, payroll rules must be effective-dated and calculation steps must remain explainable. The Ministry of Employment and Labor's wage-statement guidance requires relevant payment and deduction items and calculation methods for variable components such as hourly, daily, overtime, night, and holiday work.

A safer first HCM release is employee, contract, attendance, time, leave, and payroll-export integration. Do not claim a complete Korean payroll engine until external domain review and versioned statutory tests exist.

---

## 7. Unified store application

The store product should be an operational front end over the same party, catalog, pricing, inventory, order, payment, and accounting modules. It should not maintain a separate "store database" that later synchronizes loosely with ERP.

### 7.1 Goods selling

```
Catalog and price snapshot
 -> cart or quotation
 -> stock availability
 -> stock reservation
 -> payment authorization/capture
 -> sales order
 -> pickup/shipping/fulfillment
 -> immutable stock movement
 -> invoice/receipt and accounting posting
 -> return/refund/credit note
```

Critical invariants:

- order, payment, and fulfillment have separate state machines;
- stock is reserved before order commitment;
- reservations expire and release stock;
- every mutation carries an idempotency key;
- payment webhooks are verified and deduplicated;
- price, discount, and tax decisions are snapshotted and explainable;
- POS shift-close reconciles expected and actual cash/card/channel settlements.

### 7.2 Rental rooms, video rooms, and seats

Use one ReservableResource model with four allocation modes:

| Mode | Examples | Conflict policy |
|---|---|---|
| Exclusive unit | room, studio, equipment | No overlapping booking |
| Capacity pool | shared room/session | Sum of quantities cannot exceed capacity |
| Assigned seat | theater, video room, desk | Selected seat unavailable for overlapping session |
| Flexible area | restaurant tables | Tables may merge or split under allocation policy |

Core entities: venue and resource type; resource unit/group; versioned seat map; opening hours, blackout, maintenance window; availability calendar; price/rate plan; hold with server-side TTL; booking and participants; deposit and cancellation policy; waitlist and no-show; check-in, usage, extension, check-out; damage, overtime, fine, refund, cleaning/maintenance buffer.

A payment success must never be assumed to imply booking success. The reconciliation queue must detect: paid but not confirmed; confirmed but unpaid; refunded but still allocated; expired hold with an in-flight payment callback.

### 7.3 Restaurant package

**Applications**

| Screen | User |
|---|---|
| Customer table tablet | Seated customer |
| QR/mobile self-order | Customer's phone |
| Self-order kiosk | Walk-in/takeout customer |
| Waiter floor screen | Floor employee |
| Cashier/POS | Cashier |
| Kitchen display | Kitchen/bar |
| Reservation desk | Host/manager |
| Menu and stock admin | Manager |
| Employee workspace | Staff |
| Enterprise admin | Finance/HR/procurement/owner |
| Device manager | IT/operations |

**Domain model:** venue, floor, table, seat, section; reservation, waitlist, arrival, seating; table session and device session; menu and version; category, item, combo; modifier group and option; allergens and availability; order, line, course, service type; kitchen station and preparation ticket; item preparation status; bill, split, merge, discount, service charge, payment; recipe/BOM and ingredient stock consumption.

**Korea-style table tablet.** A table tablet must be a managed enterprise device, not a public URL containing a table number.

Required controls: provisioned device identity or certificate; tenant/location/table assignment; kiosk lockdown; remote revoke and re-provision; signed menu/configuration snapshots; Korean/English and accessibility modes; real-time sold-out and price updates; local pending-command journal; idempotent order commands; heartbeat and stale-device alert; staff-call and bill-request events; automatic session reset after table close; no raw card data stored on the device.

**Restaurant lifecycle**

```
Reservation or walk-in
 -> table/party session
 -> versioned menu snapshot
 -> customer or waiter adds items/modifiers
 -> validation and price snapshot
 -> route lines to kitchen/bar stations
 -> prepare -> ready -> served
 -> additional rounds/courses
 -> table/order transfer or merge
 -> bill split/payment
 -> close table
 -> recipe stock consumption
 -> accounting and settlement posting
```

A credible first release should match the current baseline exposed by established products: temporary-network-outage support, self-ordering, floor/table status, bookings, kitchen notifications/display, order transfer/merge, courses, split bills, payments, and employee operation. Odoo's current POS and restaurant documentation exposes these as integrated capabilities rather than separate applications.

---

## 8. Amazon and other web-store integration

Create a Channel Hub, not Amazon code inside the sales module.

```
Catalog / Inventory / Sales / Finance
                 |
             Channel Hub
                 |
       +---------+----------+
       |         |          |
     Amazon   Korean mall   Other store
```

Canonical operations: authorize or revoke a seller account; import marketplace schema/product types; publish and update listings; update price and available quantity; receive/import orders; acknowledge orders; publish fulfillment and tracking; cancel and refund; receive returns; import fees, settlements, and payouts; reconcile external and internal state.

Each adapter requires: per-tenant OAuth/token vault; least-privilege scopes; raw notification inbox with signature metadata; provider-event deduplication; pull cursor/checkpoint; per-operation adaptive rate limiting; retry classification and exponential backoff with jitter; dead-letter queue and operator replay; versioned mapping; redacted request/response audit; periodic full reconciliation; kill switch per tenant, adapter, and operation.

Amazon SP-API publishes operation-specific rate limits, supports event notifications through SQS or EventBridge, and provides static and dynamic sandbox facilities. This makes an asynchronous, checkpointed, rate-aware connector mandatory; a synchronous API passthrough from a user request would be unreliable.

Rollout order:

1. Generic channel SPI and deterministic mock adapter.
2. Amazon private application for one pilot seller.
3. One Korean marketplace selected by the pilot customer.
4. Shopify or another general web-store adapter.
5. Additional channels only after reconciliation and canonical mappings are stable.

---

## 9. Security, payment, and operational architecture

**Identity and authorization:** OIDC/OAuth identity integration; MFA for privileged roles; short-lived and revocable sessions; RBAC plus tenant, company, location, ownership, amount, device, and shift attributes; server-side object and function authorization; segregation of duties for refunds, price overrides, journal posting, payroll, and user administration; service/device roles narrower than human roles.

**Payments:** hosted payment pages or hosted fields; certified payment terminals; provider tokens and masked references; verified and deduplicated webhooks; independent settlement reconciliation. Do not store PAN or CVV. The actual payment architecture must be assessed against PCI DSS v4.0.1; PCI SSC describes the standard as applying to entities that store, process, transmit, or can affect the security of payment-account data.

**Observability.** Every synchronous and asynchronous operation should carry: request and trace ID; tenant and location; actor, service, or device identity; command and idempotency key; order, booking, payment, ticket, or external-channel ID; safe machine-readable error code.

Operational dashboards must cover: API latency/errors/saturation; database connections, locks, replica lag, backup status; outbox and worker lag; payment reconciliation; marketplace rate limits and dead letters; device/table/KDS health; expired holds and booking conflicts; stock mismatch and negative availability; security and privilege events.

---

## 10. Parallel-agent implementation plan

### 10.1 Freeze shared contracts first

Before broad parallel coding, freeze:

1. TenantContext, ActorContext, DeviceContext
2. Money, Quantity, TimeRange, typed IDs
3. CommandEnvelope, CommandResult, ErrorCode
4. DomainEvent, OutboxRecord, AuditRecord
5. Repository, UnitOfWork, Transaction, migration interfaces
6. authorization decision interface
7. API versioning, JSON, pagination, and error conventions
8. product, order, stock-reservation, payment, booking, and table-session identities
9. modern sspec contract/fixture format
10. observability field names

A frozen-contract change requires an ADR, compatibility analysis, migration plan, and integration-owner review.

### 10.2 Agent lanes

| Lane | Exclusive ownership | Initial deliverable |
|---|---|---|
| L0 Architecture/integration | ADRs, contracts, module graph, merge train | Contract v1 and product layout |
| L1 Toolchain/build | Compiler pinning, CI, build cache, reproducibility | Admitted build/test toolchain without unexplained exit 139 |
| L2 HTTP/API | Shared protocol core, routing, API framework, proxy policy | Hardened private HTTP/1 API |
| L3 Persistence | PostgreSQL adapter, pool, migrations, transactions, outbox, SQLite edge | Durable repository/unit-of-work layer |
| L4 Identity/foundation | Tenant, organization, party, user, role, device, approval, audit | Cross-tenant-safe foundation |
| L5 Catalog/inventory/procurement | Product, price, stock ledger/reservation, PO/receipt | Sellable SKU and stock truth |
| L6 CRM/sales/finance | Lead, deal, quote, order, invoice, payment posting, GL MVP | Quote-to-cash vertical |
| L7 Booking/rental | Resources, calendars, holds, seats, deposit, check-in/out | Room/seat rental vertical |
| L8 Restaurant/device | Menu, table session, order, kitchen ticket, KDS, device gateway | Table-order vertical |
| L9 Web/POS/admin UX | Customer, POS, waiter, KDS, employee, admin workspaces | Role-oriented usable workflows |
| L10 Channel Hub | Adapter SPI, inbox, rate limiting, mappings, reconciliation | Amazon pilot |
| L11 Security/QA/SRE | Threat model, test harness, deployment, recovery, observability | Continuous admission evidence |
| L12 HCM/Korea pack | Employee, contract, attendance, leave, payroll boundary | HCM MVP and reviewed integration pack |

### 10.3 Delivery waves

**Wave 0 — Product boundary and contracts.** Deliver: standalone product repository; pinned toolchain; reproducible build/test environment; classification of prototype versus production code; shared contracts; schema and migration conventions; PostgreSQL, edge, and deployment ADRs. Exit: every agent can build and run the same admitted suite from a clean environment.

**Wave 1 — Production foundation** (L2, L3, L4, L11). Deliver: private hardened API; PostgreSQL transactions, migrations, and outbox; identity, tenant, party, device, and RBAC; cryptographic audit; tracing, metrics, logs; backup, PITR, and restore automation. Exit: a durable tenant-isolated command survives restart and tested restore without duplicate effects.

**Wave 2 — Goods-selling vertical** (L5, L6, L9). Deliver: product/SKU/barcode; price and tax snapshot; customer and CRM deal; cart/quotation/order; payment state; stock reservation, fulfillment, and return; balanced journal posting; cashier and admin screens. Exit: one complete sale through UI → API → database → stock → payment → journal, including retry, refund, and restore.

**Wave 3 — Rental and restaurant** (L7, L8, L9). Deliver: room/resource/seat calendar and holds; deposit, check-in/out, extension, damage; floor/table/reservation; table tablet; waiter and cashier screens; KDS and kitchen routing; offline journal and reconciliation. Exit: concurrent overlap tests pass, and restaurant service continues through a temporary network interruption without duplicate orders.

**Wave 4 — Channels and enterprise breadth** (L10, L12, procurement and finance expansion). Deliver: Amazon listing/order/inventory/fulfillment/settlement pilot; employee, contract, attendance, time, and leave; purchase-to-pay; AR/AP, bank and marketplace reconciliation; country-pack interfaces. Exit: an external order reconciles through stock, fulfillment, fees, payout, and accounting exactly once.

**Wave 5 — Pilot admission.** Deliver: load and soak testing; fault injection; tenant-isolation assessment; penetration review; backup/restore and failover drills; migration rehearsal; runbooks and operator training; one limited tenant/location pilot.

---

## 11. Immediate P0 backlog

1. Establish simple-enterprise as the product repository.
2. Pin and admit one stable Simple compiler/runtime.
3. Close current native container/row-materialization defects.
4. Freeze foundation, command, repository, event, and API contracts.
5. Implement PostgreSQL pooling, transactions, migrations, and outbox.
6. Merge sync/async HTTP parsing, routing, limits, and path safety.
7. Integrate live identity, tenant context, devices, and DB-enforced isolation.
8. Replace toy audit/durable hashes with cryptographic database-backed audit records.
9. Build the complete goods-sale proving vertical.
10. Add booking/rental and restaurant only after the shared product, stock, payment, and finance contracts are stable.

Explicitly defer: making the custom Simple DB server an ERP dependency; direct public Simple TLS/HTTP/2; microservice decomposition of transactional core domains; universal event sourcing; raw payment-card storage; many marketplace adapters at once; claims of complete Korean payroll/tax compliance without reviewed evidence.

---

## Final recommendation

Build the package around three proving verticals:

1. **Goods sale:** catalog → stock → payment → fulfillment → return → accounting.
2. **Room/resource/seat rental:** availability → hold → booking → deposit → usage → return/damage → billing.
3. **Restaurant service:** reservation → table tablet/waiter → kitchen → bill/payment → stock/accounting.

Once these three use one durable tenant/party/product/pricing/payment/inventory/finance foundation and pass recovery and security gates, CRM, procurement, HCM, external marketplaces, support, projects, and analytics can grow in parallel without becoming disconnected applications.
