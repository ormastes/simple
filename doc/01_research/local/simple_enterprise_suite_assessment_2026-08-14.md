# Simple Enterprise Suite — Repository Assessment, Target Architecture, and Parallel-Agent Delivery Plan

**Repositories reviewed:** `ormastes/simple` and the split-out `ormastes/simple-erp`
**Assessment date:** 2026-08-14
**Status:** Research and design proposal; no repository changes were made by this assessment
**Related:** [`simple_erp.md`](simple_erp.md) (local research lane), `doc/04_architecture/simple_erp.md`, `doc/05_design/simple_erp.md`

---

# Part I — Executive verdict

The repository does **not yet contain a full enterprise solution**. It contains a tested and
well-structured **business-framework prototype** that is useful as the seed of a larger product.

The existing implementation already demonstrates:

* a common guarded-write path;
* tenant/session checks and role-based authorization;
* validation and idempotency;
* approval decisions;
* event, projection, posting, snapshot, and recovery concepts;
* small CRM, sales, reservation, marketplace, and restaurant domains;
* interpreter-mode specifications;
* a static HTML dashboard.

However, both the monorepo example and the standalone `ormastes/simple-erp` repository explicitly
describe themselves as in-memory implementations, and their readiness documentation blocks
production use until durable storage, live identity/secrets, automated recovery, monitoring,
migration, and deployment controls exist.

My scope-weighted estimate is:

> **Approximately 8–12% of the requested executable enterprise product exists.**

This is a heuristic estimate of product capability, not LOC coverage. Architecture documentation is
considerably further ahead than integrated functionality.

---

## 1. Current implementation assessment

### 1.1 Maturity matrix

Scale:

* **0:** absent
* **1:** isolated model or helper
* **2:** tested prototype
* **3:** integrated durable MVP
* **4:** pilot-ready
* **5:** enterprise production

| Area                               | Current state                                                | Level |
| ---------------------------------- | ------------------------------------------------------------ | ----: |
| Enterprise capability architecture | Broad UBS/MDSOC+ enterprise blueprint                        |     2 |
| Shared guarded-write framework     | Session → RBAC → validation → idempotency, approval overlay  |     2 |
| Event, projection, posting kernel  | Tested architectural examples                                |     2 |
| CRM                                | One lead record and pipeline-stage movement                  |     1 |
| Sales                              | Subtotal, tax, payment flag, and status helpers              |     1 |
| Inventory                          | Small availability and fulfillment examples                  |     1 |
| Reservation                        | Capacity, hold, cancel, and no-show helpers                  |     1 |
| Rental                             | No complete rental lifecycle                                 |     0 |
| Restaurant                         | Minimal menu item and table-order state machine              |     1 |
| Marketplace                        | Listing, stock, commission, and payout calculations          |     1 |
| Accounting                         | Balanced posting concepts, but no operational general ledger |     1 |
| Procurement                        | No integrated requisition-to-payment flow                    |     0 |
| HR/HCM/payroll                     | No product implementation                                    |     0 |
| Employee/admin UI                  | Static KPI dashboard only                                    |     1 |
| Customer/POS/table/KDS UI          | Not implemented                                              |     0 |
| Live application API               | Pure route simulation; no integrated application server      |     0 |
| Production database                | Explicitly blocked                                           |     0 |
| Recovery and operations            | Helpers and documentation, not deployed automation           |     1 |
| Production security assurance      | Selected controls and unit specs only                        |     1 |

The domain files confirm that CRM is currently a `Lead`, reservations are a capacity counter, sales
are basic totals/status, marketplace support is a local listing/order calculation, and restaurant
support is a small forward-only order state machine.

There is meaningful testing around the kernel, domains, routing, approval, reporting, snapshots,
durable log, commit queue, and organization rules. These tests currently operate mainly through the
interpreter and pure function interfaces rather than a live browser → server → database system.

### 1.2 What should be preserved

The strongest existing components are:

1. **The common guarded-write rule.** Domain modules cannot independently bypass session,
   authorization, validation, or idempotency checks.
2. **Registry-driven domain extension.**
3. **Explicit accepted/denied results.**
4. **Approval as a shared concern.**
5. **Immutable posting and event concepts.**
6. **Interpreter specifications as executable design evidence.**
7. **MDSOC+ module ownership and restricted visibility.**

The current `durable_log.spl` should not become the production ledger. Its source explicitly
describes its checksum as a toy, non-cryptographic digest; it also writes a complete line-oriented
file rather than participating in an ACID database transaction. It remains useful for fixtures,
export, and recovery experiments.

---

## 2. Repository and product boundary

Use the repositories as follows:

### `ormastes/simple`

Owns:

* Simple language and compiler;
* runtime;
* standard libraries;
* web-server framework;
* database adapters;
* UI framework;
* OS and hardware support;
* common testing and documentation infrastructure.

It should retain only a small enterprise compatibility example and smoke tests.

### `ormastes/simple-erp`, renamed or evolved into `simple-enterprise`

Owns:

* the enterprise product;
* database schema and migrations;
* business modules;
* web/POS/table/KDS applications;
* deployment configuration;
* integration adapters;
* operational runbooks;
* country packs.

The standalone repository currently contains substantially the same prototype sources as the
monorepo example and still identifies itself as an in-memory implementation. It is nevertheless the
correct product boundary because enterprise releases should not be coupled to unrelated compiler,
OS, RISC-V, browser, and rendering changes.

A useful working name is:

> **Simple Enterprise Suite**, internally organized using the existing
> **Unified Business Suite / MDSOC+** architecture.

---

## 3. Web-server robustness assessment

The server infrastructure is more advanced than the ERP application. The asynchronous server
includes worker event loops, `SO_REUSEPORT`, incremental HTTP parsing, HTTP/2 structures, TLS/ALPN,
compression, static files, range responses, middleware, and graceful draining.

It is still not ready to be the directly exposed public edge of a payment- and identity-bearing
enterprise product.

### 3.1 Critical issue: sync/async security divergence

Recent hardening was explicitly applied to `nogc_sync_mut/http_server`: request limits, path-safety
checks, duplicate `Content-Length` rejection, and fail-closed behavior for unsupported chunking. The
async server has a separate parser and router and therefore does not automatically inherit those
controls. The hardening record also notes unresolved end-to-end bounded-read evidence and some
pre-existing security-test import failures.

This duplication should be removed:

```text
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

Both transports must consume the same protocol core and run the same conformance, fuzz, and
request-smuggling corpus.

### 3.2 Release-blocking async-server findings

#### Request limits are applied too late

The async parser grows its buffer and materializes the request body, while the middleware
body-size check runs after request parsing. That does not reliably prevent memory exhaustion by a
declared or streamed oversized body. The reviewed async parser also does not visibly enforce the
sync implementation's request-line, header-count, and per-header limits.

Limits must be enforced during parsing, before buffer growth:

* request-line bytes;
* total header bytes;
* header count;
* individual header bytes;
* declared body bytes;
* decoded chunk bytes;
* multipart field and file bytes;
* route-specific upload limits.

#### Static-path confinement is not shared

The reviewed async worker constructs static paths from `root + request.path`, and the async router
does not invoke the sync router's `path_is_safe` guard.

Required behavior:

1. Decode according to one canonical policy.
2. Reject NUL, backslash, encoded separators, double encoding, and traversal.
3. Canonicalize the final path.
4. Verify that it remains beneath the configured root.
5. Prefer descriptor-relative open APIs where available.
6. Initially serve static files at the edge proxy rather than the application process.

#### Dynamic handler dispatch needs a live proof

In the reviewed request path, a successful route match appears to invoke the inline static handler
directly, despite separate handler-registry and security-context dispatch functions being present.
This may be incomplete wiring rather than intended behavior. A live system test must prove that API
routes call the requested dynamic handler under a server-established security context.

#### Native runtime correctness is a production blocker

The async worker contains repeated workarounds stating that `Dict.get()` can return corrupted class
or struct payloads in native code generation. The latest repository note also records that focused
checks using the deployed pure-Simple executable terminate with signal 11, exit code 139.

An enterprise product cannot admit a runtime with known container-materialization corruption. This
needs:

* minimized compiler/runtime regression cases;
* sanitizer-enabled native builds where supported;
* interpreter/native differential tests;
* forced admission gates for arrays, dictionaries, optionals, results, rows, and nested business
  aggregates;
* removal of workaround-only acceptance criteria once the defect is fixed.

#### Direct public TLS/HTTP/2 should be deferred

The reviewed worker performs TLS handshake work synchronously in the accept flow, allowing a slow
handshake to occupy a worker. HTTP/2 also needs strict preface, HPACK, stream, frame, memory, and
concurrency limits.

Initial deployment should therefore be:

```text
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

Direct Simple TLS/H2 exposure becomes a later platform milestone, not a prerequisite for the
enterprise package.

### 3.3 Web-server admission gate

The server becomes eligible for direct enterprise use only when:

* sync and async use one parser/router/security core;
* all limits are enforced before allocation;
* path confinement is end-to-end tested;
* dynamic route dispatch is proven;
* native corruption defects are closed;
* slow-header, slow-body, partial-I/O, and pending-write limits pass;
* parser, path, multipart, range, TLS, HTTP/2, and proxy fuzzing passes;
* request-smuggling differential tests against the selected proxy pass;
* ASVS and API authorization controls have traceable test evidence.

OWASP positions ASVS 5.0.0 as the current stable, verifiable application-security standard.
API-specific testing must additionally cover object- and function-level authorization, resource
exhaustion, sensitive-business-flow automation, SSRF, API inventory, and unsafe consumption of
third-party APIs. ([1])

---

## 4. Database decision

### 4.1 Do not make Simple DB the enterprise dependency yet

The current repository documentation says:

* the operational tier is an embedded SDN/file database;
* the historical full MVCC/WAL implementation is an unfinished skeleton and is absent from the
  current worktree;
* the SimpleOS database service is a small bounded store, not a general database server;
* PostgreSQL/libSQL drivers, pooling, transactions, mapping, and introspection remain planned work.

The current performance report also records:

* server mode unavailable;
* unsafe native row/scalar materialization;
* corrupted query-result lengths;
* a focused native probe terminating with exit 139;
* current timings not being acceptable as correctness evidence.

Therefore:

> **Finance, payroll, customer PII, payment state, booking truth, and inventory truth must not use
> Simple DB in the first production package.**

Keep Simple DB as a separate research and compatibility track.

### 4.2 Use PostgreSQL as the system of record

Recommended first-production topology:

```text
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

PostgreSQL provides database-enforced row-security policies, WAL-based point-in-time recovery,
standby operation, and range exclusion constraints that can prevent overlapping reservations at the
database level. ([2])

Core rules:

* one PostgreSQL cluster and modular schemas initially;
* every tenant-owned table includes `tenant_id`;
* application roles do not own tables or have `BYPASSRLS`;
* use `FORCE ROW LEVEL SECURITY` where appropriate;
* tenant context is set by the authenticated server, never trusted from request JSON;
* business commands and outbox rows commit in one transaction;
* idempotency keys are unique database constraints;
* financial and stock postings are append-only;
* exclusive bookings use range exclusion constraints or equivalent serializable locking;
* use expand → backfill → contract migrations;
* restore and reconciliation tests are release gates.

### 4.3 SQLite is suitable for bounded offline edge use

A real SQLite runtime binding and Simple wrapper already support open/close, prepared statements,
typed binds, queries, and transaction calls.

Use it for:

* offline retail POS commands;
* restaurant table-tablet pending orders;
* local KDS continuity;
* demos and developer mode.

Before admission, add:

* migration/version tables;
* WAL and busy-timeout configuration;
* enforced foreign keys;
* prepared-statement-only repositories;
* typed row mapping;
* encrypted token storage;
* power-loss, disk-full, and corruption tests;
* a bounded local operation journal;
* idempotent server replay;
* cursor and reconciliation logic;
* reset and re-provision procedures.

SQLite must remain a cache and pending-command store, not the enterprise source of truth.

---

## 5. Target architecture

Use a **modular monolith first**, because the critical workflows require atomic transactions across
several domains.

```text
Customer Web/PWA      POS/Kiosk      Table Tablet      Employee/Admin
        \                 |                |                 /
                    Edge proxy
                         |
               Simple application
  +------------------------------------------------------+
  | Foundation | CRM | Sales | Catalog | Inventory        |
  | Procurement | Finance | Booking/Rental | Restaurant   |
  | HCM | Support | Channel Hub | Analytics               |
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

Extract separate processes only for:

* marketplace connectors;
* notifications;
* document/media processing;
* analytics/search;
* restaurant/POS device gateway.

Do **not** begin with microservices for sales, inventory, payment, booking, and finance. Their
invariants are easier to preserve inside one transactional process.

### 5.1 Shared enterprise foundation

Freeze and implement these before individual modules grow:

* tenant, legal entity, business unit, location, cost center;
* party, person, organization, customer, supplier, employee linkage;
* identity, actor, session, service account, device identity;
* money, currency, quantity, unit, tax class, time range;
* typed IDs and optimistic aggregate versions;
* permission and policy decisions;
* approval, delegation, segregation of duties;
* document numbering and status transitions;
* audit records;
* idempotency;
* repository, unit of work, transaction, migration, outbox;
* localization, retention, privacy request, notification, attachment.

---

## 6. Enterprise package modules

| Package             | Required scope                                                                      |
| ------------------- | ----------------------------------------------------------------------------------- |
| Foundation          | Tenants, companies, locations, users, devices, roles, approvals, audit, workflow     |
| Party and CRM       | Leads, accounts, contacts, activities, opportunities, quotes, contracts              |
| Sales               | Cart, quotation, order, fulfillment, invoice request, return, customer credit        |
| Catalog and pricing | Product, variant, SKU, barcode, bundle, menu link, price lists, tax, promotions      |
| Inventory/WMS       | Warehouses, bins, lots/serials, stock ledger, reservation, transfer, picking, count  |
| Procurement         | Requisition, RFQ, supplier quote, PO, receipt, purchase invoice, replenishment       |
| Finance             | Chart of accounts, journals, AR/AP, tax, payment allocation, reconciliation, close   |
| Booking             | Time-ranged resources, capacity pools, assigned seats, waitlists, holds              |
| Rental              | Rate plans, deposits, check-in/out, extension, damage, fines, maintenance            |
| Restaurant          | Reservation, floor/table, table session, menu/modifiers, kitchen tickets, bills      |
| HCM                 | Employee, position, contract, attendance, shift, leave, expense, onboarding          |
| Payroll boundary    | Effective-dated inputs, calculation evidence, payslip, accounting export             |
| Channel Hub         | Amazon and other store adapters, mappings, notifications, reconciliation             |
| Support/projects    | Cases, SLA, projects, tasks, time, expenses                                          |
| Analytics           | Operational reporting, finance reports, warehouse export, governed AI assistance     |

For the Korean country pack, payroll rules must be effective-dated and calculation steps must remain
explainable. The Ministry of Employment and Labor's wage-statement guidance requires relevant
payment and deduction items and calculation methods for variable components such as hourly, daily,
overtime, night, and holiday work. ([3])

A safer first HCM release is employee, contract, attendance, time, leave, and payroll-export
integration. Do not claim a complete Korean payroll engine until external domain review and
versioned statutory tests exist.

---

## 7. Unified store application

The store product should be an operational front end over the same party, catalog, pricing,
inventory, order, payment, and accounting modules. It should not maintain a separate "store
database" that later synchronizes loosely with ERP.

### 7.1 Goods selling

```text
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

* order, payment, and fulfillment have separate state machines;
* stock is reserved before order commitment;
* reservations expire and release stock;
* every mutation carries an idempotency key;
* payment webhooks are verified and deduplicated;
* price, discount, and tax decisions are snapshotted and explainable;
* POS shift-close reconciles expected and actual cash/card/channel settlements.

### 7.2 Rental rooms, video rooms, and seats

Use one `ReservableResource` model with four allocation modes:

| Mode           | Examples                  | Conflict policy                                   |
| -------------- | ------------------------- | ------------------------------------------------- |
| Exclusive unit | room, studio, equipment   | No overlapping booking                            |
| Capacity pool  | shared room/session       | Sum of quantities cannot exceed capacity          |
| Assigned seat  | theater, video room, desk | Selected seat unavailable for overlapping session |
| Flexible area  | restaurant tables         | Tables may merge or split under allocation policy |

Core entities:

* venue and resource type;
* resource unit/group;
* versioned seat map;
* opening hours, blackout, maintenance window;
* availability calendar;
* price/rate plan;
* hold with server-side TTL;
* booking and participants;
* deposit and cancellation policy;
* waitlist and no-show;
* check-in, usage, extension, check-out;
* damage, overtime, fine, refund, cleaning/maintenance buffer.

A payment success must never be assumed to imply booking success. The reconciliation queue must
detect:

* paid but not confirmed;
* confirmed but unpaid;
* refunded but still allocated;
* expired hold with an in-flight payment callback.

### 7.3 Restaurant package

#### Applications

| Screen                | User                         |
| --------------------- | ---------------------------- |
| Customer table tablet | Seated customer              |
| QR/mobile self-order  | Customer's phone             |
| Self-order kiosk      | Walk-in/takeout customer     |
| Waiter floor screen   | Floor employee               |
| Cashier/POS           | Cashier                      |
| Kitchen display       | Kitchen/bar                  |
| Reservation desk      | Host/manager                 |
| Menu and stock admin  | Manager                      |
| Employee workspace    | Staff                        |
| Enterprise admin      | Finance/HR/procurement/owner |
| Device manager        | IT/operations                |

#### Domain model

* venue, floor, table, seat, section;
* reservation, waitlist, arrival, seating;
* table session and device session;
* menu and version;
* category, item, combo;
* modifier group and option;
* allergens and availability;
* order, line, course, service type;
* kitchen station and preparation ticket;
* item preparation status;
* bill, split, merge, discount, service charge, payment;
* recipe/BOM and ingredient stock consumption.

#### Korea-style table tablet

A table tablet must be a managed enterprise device, not a public URL containing a table number.

Required controls:

* provisioned device identity or certificate;
* tenant/location/table assignment;
* kiosk lockdown;
* remote revoke and re-provision;
* signed menu/configuration snapshots;
* Korean/English and accessibility modes;
* real-time sold-out and price updates;
* local pending-command journal;
* idempotent order commands;
* heartbeat and stale-device alert;
* staff-call and bill-request events;
* automatic session reset after table close;
* no raw card data stored on the device.

#### Restaurant lifecycle

```text
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

A credible first release should match the current baseline exposed by established products:
temporary-network-outage support, self-ordering, floor/table status, bookings, kitchen
notifications/display, order transfer/merge, courses, split bills, payments, and employee operation.
Odoo's current POS and restaurant documentation exposes these as integrated capabilities rather than
separate applications. ([4])

---

## 8. Amazon and other web-store integration

Create a **Channel Hub**, not Amazon code inside the sales module.

```text
Catalog / Inventory / Sales / Finance
                 |
             Channel Hub
                 |
       +---------+----------+
       |         |          |
     Amazon   Korean mall   Other store
```

Canonical operations:

* authorize or revoke a seller account;
* import marketplace schema/product types;
* publish and update listings;
* update price and available quantity;
* receive/import orders;
* acknowledge orders;
* publish fulfillment and tracking;
* cancel and refund;
* receive returns;
* import fees, settlements, and payouts;
* reconcile external and internal state.

Each adapter requires:

* per-tenant OAuth/token vault;
* least-privilege scopes;
* raw notification inbox with signature metadata;
* provider-event deduplication;
* pull cursor/checkpoint;
* per-operation adaptive rate limiting;
* retry classification and exponential backoff with jitter;
* dead-letter queue and operator replay;
* versioned mapping;
* redacted request/response audit;
* periodic full reconciliation;
* kill switch per tenant, adapter, and operation.

Amazon SP-API publishes operation-specific rate limits, supports event notifications through SQS or
EventBridge, and provides static and dynamic sandbox facilities. This makes an asynchronous,
checkpointed, rate-aware connector mandatory; a synchronous API passthrough from a user request
would be unreliable. ([5])

Rollout order:

1. Generic channel SPI and deterministic mock adapter.
2. Amazon private application for one pilot seller.
3. One Korean marketplace selected by the pilot customer.
4. Shopify or another general web-store adapter.
5. Additional channels only after reconciliation and canonical mappings are stable.

---

## 9. Security, payment, and operational architecture

### Identity and authorization

Use:

* OIDC/OAuth identity integration;
* MFA for privileged roles;
* short-lived and revocable sessions;
* RBAC plus tenant, company, location, ownership, amount, device, and shift attributes;
* server-side object and function authorization;
* segregation of duties for refunds, price overrides, journal posting, payroll, and user
  administration;
* service/device roles narrower than human roles.

### Payments

Prefer:

* hosted payment pages or hosted fields;
* certified payment terminals;
* provider tokens and masked references;
* verified and deduplicated webhooks;
* independent settlement reconciliation.

Do not store PAN or CVV. The actual payment architecture must be assessed against PCI DSS v4.0.1;
PCI SSC describes the standard as applying to entities that store, process, transmit, or can affect
the security of payment-account data. ([6])

### Observability

Every synchronous and asynchronous operation should carry:

* request and trace ID;
* tenant and location;
* actor, service, or device identity;
* command and idempotency key;
* order, booking, payment, ticket, or external-channel ID;
* safe machine-readable error code.

Operational dashboards must cover:

* API latency/errors/saturation;
* database connections, locks, replica lag, backup status;
* outbox and worker lag;
* payment reconciliation;
* marketplace rate limits and dead letters;
* device/table/KDS health;
* expired holds and booking conflicts;
* stock mismatch and negative availability;
* security and privilege events.

---

## 10. Parallel-agent implementation plan

### 10.1 Freeze shared contracts first

Before broad parallel coding, freeze:

1. `TenantContext`, `ActorContext`, `DeviceContext`
2. `Money`, `Quantity`, `TimeRange`, typed IDs
3. `CommandEnvelope`, `CommandResult`, `ErrorCode`
4. `DomainEvent`, `OutboxRecord`, `AuditRecord`
5. `Repository`, `UnitOfWork`, `Transaction`, migration interfaces
6. authorization decision interface
7. API versioning, JSON, pagination, and error conventions
8. product, order, stock-reservation, payment, booking, and table-session identities
9. modern sspec contract/fixture format
10. observability field names

A frozen-contract change requires an ADR, compatibility analysis, migration plan, and
integration-owner review.

### 10.2 Agent lanes

| Lane                             | Exclusive ownership                                                     | Initial deliverable                                        |
| -------------------------------- | ----------------------------------------------------------------------- | ---------------------------------------------------------- |
| L0 Architecture/integration      | ADRs, contracts, module graph, merge train                              | Contract v1 and product layout                             |
| L1 Toolchain/build               | Compiler pinning, CI, build cache, reproducibility                      | Admitted build/test toolchain without unexplained exit 139 |
| L2 HTTP/API                      | Shared protocol core, routing, API framework, proxy policy              | Hardened private HTTP/1 API                                |
| L3 Persistence                   | PostgreSQL adapter, pool, migrations, transactions, outbox, SQLite edge | Durable repository/unit-of-work layer                      |
| L4 Identity/foundation           | Tenant, organization, party, user, role, device, approval, audit        | Cross-tenant-safe foundation                               |
| L5 Catalog/inventory/procurement | Product, price, stock ledger/reservation, PO/receipt                    | Sellable SKU and stock truth                               |
| L6 CRM/sales/finance             | Lead, deal, quote, order, invoice, payment posting, GL MVP              | Quote-to-cash vertical                                     |
| L7 Booking/rental                | Resources, calendars, holds, seats, deposit, check-in/out               | Room/seat rental vertical                                  |
| L8 Restaurant/device             | Menu, table session, order, kitchen ticket, KDS, device gateway         | Table-order vertical                                       |
| L9 Web/POS/admin UX              | Customer, POS, waiter, KDS, employee, admin workspaces                  | Role-oriented usable workflows                             |
| L10 Channel Hub                  | Adapter SPI, inbox, rate limiting, mappings, reconciliation             | Amazon pilot                                               |
| L11 Security/QA/SRE              | Threat model, test harness, deployment, recovery, observability         | Continuous admission evidence                              |
| L12 HCM/Korea pack               | Employee, contract, attendance, leave, payroll boundary                 | HCM MVP and reviewed integration pack                      |

### 10.3 Delivery waves

#### Wave 0 — Product boundary and contracts

Deliver:

* standalone product repository;
* pinned toolchain;
* reproducible build/test environment;
* classification of prototype versus production code;
* shared contracts;
* schema and migration conventions;
* PostgreSQL, edge, and deployment ADRs.

**Exit:** every agent can build and run the same admitted suite from a clean environment.

#### Wave 1 — Production foundation

Parallel work: L2, L3, L4, L11.

Deliver:

* private hardened API;
* PostgreSQL transactions, migrations, and outbox;
* identity, tenant, party, device, and RBAC;
* cryptographic audit;
* tracing, metrics, logs;
* backup, PITR, and restore automation.

**Exit:** a durable tenant-isolated command survives restart and tested restore without duplicate
effects.

#### Wave 2 — Goods-selling vertical

Parallel work: L5, L6, L9.

Deliver:

* product/SKU/barcode;
* price and tax snapshot;
* customer and CRM deal;
* cart/quotation/order;
* payment state;
* stock reservation, fulfillment, and return;
* balanced journal posting;
* cashier and admin screens.

**Exit:** one complete sale through UI → API → database → stock → payment → journal, including
retry, refund, and restore.

#### Wave 3 — Rental and restaurant

Parallel work: L7, L8, L9.

Deliver:

* room/resource/seat calendar and holds;
* deposit, check-in/out, extension, damage;
* floor/table/reservation;
* table tablet;
* waiter and cashier screens;
* KDS and kitchen routing;
* offline journal and reconciliation.

**Exit:** concurrent overlap tests pass, and restaurant service continues through a temporary
network interruption without duplicate orders.

#### Wave 4 — Channels and enterprise breadth

Parallel work: L10, L12, procurement and finance expansion.

Deliver:

* Amazon listing/order/inventory/fulfillment/settlement pilot;
* employee, contract, attendance, time, and leave;
* purchase-to-pay;
* AR/AP, bank and marketplace reconciliation;
* country-pack interfaces.

**Exit:** an external order reconciles through stock, fulfillment, fees, payout, and accounting
exactly once.

#### Wave 5 — Pilot admission

Deliver:

* load and soak testing;
* fault injection;
* tenant-isolation assessment;
* penetration review;
* backup/restore and failover drills;
* migration rehearsal;
* runbooks and operator training;
* one limited tenant/location pilot.

---

## 11. Immediate P0 backlog

The first implementation sequence should be:

1. Establish `simple-enterprise` as the product repository.
2. Pin and admit one stable Simple compiler/runtime.
3. Close current native container/row-materialization defects.
4. Freeze foundation, command, repository, event, and API contracts.
5. Implement PostgreSQL pooling, transactions, migrations, and outbox.
6. Merge sync/async HTTP parsing, routing, limits, and path safety.
7. Integrate live identity, tenant context, devices, and DB-enforced isolation.
8. Replace toy audit/durable hashes with cryptographic database-backed audit records.
9. Build the complete goods-sale proving vertical.
10. Add booking/rental and restaurant only after the shared product, stock, payment, and finance
    contracts are stable.

Explicitly defer:

* making the custom Simple DB server an ERP dependency;
* direct public Simple TLS/HTTP/2;
* microservice decomposition of transactional core domains;
* universal event sourcing;
* raw payment-card storage;
* many marketplace adapters at once;
* claims of complete Korean payroll/tax compliance without reviewed evidence.

---

## Verdict recommendation

Build the package around three proving verticals:

1. **Goods sale:** catalog → stock → payment → fulfillment → return → accounting.
2. **Room/resource/seat rental:** availability → hold → booking → deposit → usage → return/damage →
   billing.
3. **Restaurant service:** reservation → table tablet/waiter → kitchen → bill/payment →
   stock/accounting.

Once these three use one durable tenant/party/product/pricing/payment/inventory/finance foundation
and pass recovery and security gates, CRM, procurement, HCM, external marketplaces, support,
projects, and analytics can grow in parallel without becoming disconnected applications.

### External references

1. https://owasp.org/www-project-application-security-verification-standard/
2. https://www.postgresql.org/docs/17/ddl-rowsecurity.html
3. https://www.moel.go.kr/wageCal.do
4. https://www.odoo.com/documentation/19.0/applications/sales/point_of_sale.html
5. https://developer-docs.amazon.com/sp-api/docs/onboarding-overview
6. https://www.pcisecuritystandards.org/fr/document_library/

---

# Part II — Full research, design, and parallel plan

## Simple Enterprise Suite
### Repository Assessment, Target Architecture, Store/Rental/Restaurant Design, Robustness Plan, and Parallel-Agent Delivery Plan

**Repository reviewed:** `ormastes/simple` and the split-out `ormastes/simple-erp`
**Assessment date:** 2026-08-14
**Status:** Research and design proposal; no repository changes were made

---

## 1. Executive decision

The current ERP work is a useful **proof of architecture**, not a deployable enterprise product. It
already proves several valuable ideas:

- one guarded business-write path;
- tenant/session/RBAC checks;
- idempotency and explicit write outcomes;
- approval overlays;
- append-only event and posting concepts;
- five small business lanes: CRM, reservation, sale, marketplace, and restaurant;
- interpreter-mode specifications;
- a self-contained HTML KPI dashboard.

However, the requested package—CRM, ERP, HR/HCM/payroll, accounting, procurement, inventory, retail
POS, rental/seat booking, restaurant table ordering, employee/admin applications, and marketplace
integration—still lacks the production foundations that determine correctness:

- a production system of record;
- an integrated live API;
- complete identity and tenant isolation;
- real product/order/inventory/accounting models;
- payment-provider integration;
- full web/POS/table/KDS/admin user interfaces;
- reliable offline operation;
- external-channel adapters;
- backup/restore automation, observability, and security assurance.

### Recommended product strategy

1. **Use `simple` as the language/platform/toolchain repository.**
2. **Use the standalone `simple-erp` repository as the product seed**, and evolve it into
   **Simple Enterprise Suite**. Keep only a thin smoke/demo copy in the main monorepo.
3. Build a **modular monolith first**, with strict MDSOC+ module boundaries and one PostgreSQL
   transactional database.
4. Extract only independently scalable or failure-isolated processes: marketplace connectors,
   notifications, analytics, media/document processing, and the restaurant device gateway.
5. Use **PostgreSQL as the production source of truth**. Treat Simple DB as a separate experimental
   database program until it passes durability, concurrency, recovery, and security gates.
6. Merge sync and async HTTP parsing/routing/security into one shared HTTP core. Until that is
   complete, terminate TLS/HTTP/2 at a mature edge proxy and expose the Simple application only on a
   private loopback/Unix-socket HTTP/1.1 interface.
7. Do not event-source every table. Use normal transactional aggregates plus:
   - immutable accounting and stock ledgers;
   - append-only audit records;
   - a transactional outbox for integration events.

### Current scope estimate

A scope-weighted estimate places executable coverage at **approximately 8–12% of the requested
product**, with much higher coverage in architecture documentation than in integrated code.
Production deployment readiness is **blocked**, not partially complete, because the current ERP
explicitly lacks a supported durable store and live operational backends.

---

## 2. What exists today

### 2.1 Existing business-suite assets

The `simple_erp` example and split repository contain:

- `framework/guarded.spl`: common session → RBAC → validation → idempotency gate;
- `framework/org.spl`, `registry.spl`: role and lane registration;
- `kernel/event_log.spl`, `projection.spl`, `posting.spl`;
- `kernel/durable_log.spl`, `snapshot.spl`, `key_index.spl`, `commit_queue.spl`;
- domain lanes for CRM, reservation, sale, market, restaurant, and a clinic extension demo;
- dimensions for money, time, identity, permission, location, approval, audit, and communication;
- pure route dispatch and a static HTML dashboard;
- a meaningful set of interpreter specifications for kernels, dimensions, lanes, routing, reports,
  dashboards, approval, snapshots, durable log, queueing, and organization rules.

The product documentation already recognizes the decisive blocker: the application remains an
in-memory example and cannot be called production-ready until a supported durable storage façade,
live identity/secrets, automated recovery, production monitoring, migration, and deployment review
are integrated.

### 2.2 Maturity matrix

Maturity levels:

- **0 — absent**
- **1 — isolated model/helper**
- **2 — executable prototype with specifications**
- **3 — integrated MVP with durable data, live API, and usable UI**
- **4 — pilot-ready with security, recovery, and operations**
- **5 — enterprise production**

| Area | Current evidence | Level | Decision |
|---|---|---:|---|
| Enterprise feature catalog | Broad UBS/MDSOC architecture document | 2 | Reuse as capability map; rewrite into bounded-context backlogs |
| Guarded write framework | Shared fail-closed gate, approval overlay, explicit outcomes | 2 | Reuse design; replace arrays/in-memory keys with transactional repositories |
| Tenant/RBAC | Tenant/session structs and role data | 1 | Preserve contract; integrate OIDC, revocation, location/attribute rules, and DB isolation |
| Audit | Audit events and chain examples | 1 | Rebuild with cryptographic integrity, immutable storage, retention, and operator access controls |
| Event/posting kernel | Event log, projection, balanced posting examples | 2 | Reuse for ledger/outbox patterns, not universal event sourcing |
| Durable log | Line-format save/load with a documented toy checksum | 1 | Keep only as test/export utility; not authoritative storage |
| CRM | One lead model and stage movement | 1–2 | Expand to party/account/contact/deal/activity/quote/contract |
| Sales | Subtotal/tax/paid/status helpers | 1 | Replace with full quote/order/fulfillment/invoice/payment/return model |
| Reservation | Capacity, hold/book/cancel/no-show helpers | 1–2 | Replace with time-ranged resource/seat availability engine |
| Rental | No complete rental lifecycle | 0 | New bounded context on top of booking, assets, deposits, and billing |
| Restaurant | Menu item and table-order state transition helpers | 1 | New production model for venue/menu/table session/ticket/KDS/payment |
| Marketplace | Listing, commission, payout calculations | 1 | Keep domain terms; build a real channel-adapter platform |
| Product/catalog/pricing | Only lane-local examples | 0–1 | New shared product master and price/tax/promotion engine |
| Inventory/WMS | Small availability/fulfillment examples | 1 | New immutable stock ledger, reservations, warehouses, bins, lots/serials |
| Procurement | No integrated requisition/PO/receipt/AP flow | 0 | New module |
| Accounting/finance | Posting and balance examples, not a general ledger | 1 | New chart of accounts, journals, AR/AP, tax, bank reconciliation, close |
| HR/HCM/payroll | No product implementation | 0 | New module; Korean country pack and payroll integration later |
| Employee/admin UI | Static KPI HTML only | 1 | New role-oriented web/PWA workspaces |
| Customer/POS/table UI | Not implemented | 0 | New applications |
| Live ERP API | Route table explicitly has no live server | 0 | Integrate after HTTP core hardening |
| Production persistence | Explicitly blocked | 0 | PostgreSQL first; SQLite for offline edge; Simple DB research track |
| Recovery/operations | Documented checks and examples | 1 | Automate PITR, restore drills, metrics, tracing, alerts, runbooks |
| Security assurance | Some unit specs and guarded-write rules | 1 | ASVS/API-security threat model, SAST/DAST/fuzzing, penetration review |

### 2.3 The split-out repository

`ormastes/simple-erp` is not a second, more complete ERP. Its key source files are the same prototype
assets that were split from the monorepo, and its README still identifies the implementation as
in-memory and blocked on durable storage. It is nevertheless the right place to grow the product
because it establishes a clean release boundary from the large language/OS/hardware monorepo.

---

## 3. Web-server robustness assessment

The repository contains two relevant server families:

1. `nogc_sync_mut/http_server`
2. `nogc_async_mut/http_server`

The async server is structurally ambitious: worker event loops, `SO_REUSEPORT`, HTTP/1.1 parsing,
HTTP/2 structures, TLS/ALPN, compression, ranges, static files, middleware, graceful draining, and
handler registries. The sync server has a recent hardening slice with request limits, path safety,
duplicate Content-Length rejection, and chunked fail-closed behavior.

The core problem is **security divergence**: hardening was explicitly scoped to the sync
implementation, while the async worker used for scalable serving has separate parser/router code and
does not inherit all of those protections.

### 3.1 Release-blocking findings

#### P0-A — Duplicate protocol implementations

The sync server has request-limit and path-safety helpers/specs, but the async parser/router are
independent. This creates a permanent drift hazard.

**Required change:** extract shared pure modules:

```text
http_core/
  request_parser.spl
  request_limits.spl
  path_normalization.spl
  header_validation.spl
  routing.spl
  response.spl
  security_policy.spl

http_transport_sync/
http_transport_async/
```

Both transports must run the identical conformance and fuzz corpus.

#### P0-B — Async request limits are too late or absent

The async parser appends incoming data to a text buffer and materializes the body before the
middleware body-limit check runs. This does not protect memory from a declared or streaming
oversized request. The reviewed async code also lacks the sync parser's request-line, header-count,
and header-line enforcement.

**Required change:** enforce limits during parsing, before allocation/growth:

- request line;
- total header bytes;
- header count;
- per-header line;
- declared body size;
- decoded chunked size;
- multipart field/file size;
- route-specific upload policy.

#### P0-C — Async static-path confinement

The reviewed async worker constructs a static filename as `root + request.path`. The async router
itself does not call the sync `path_is_safe` guard.

**Required change:**

- percent-decode once under a defined normalization policy;
- reject NUL, backslash, encoded separators, ambiguous double encoding, and dot traversal;
- canonicalize the candidate path;
- verify it remains beneath the configured root;
- open by directory descriptor where supported to reduce time-of-check/time-of-use risk;
- initially serve static assets at the edge proxy, not from the application process.

#### P0-D — Dynamic handler dispatch must be proven

In the reviewed worker path, successful route matching calls the inline static handler directly even
though a handler registry and remote-security-context dispatch methods also exist. Before ERP
integration, a live system test must prove that each route invokes the intended dynamic handler
under the server-owned security context.

#### P0-E — Native-codegen correctness defects

The worker contains repeated workarounds because `Dict.get()` is documented as returning corrupt
class/struct payloads under native code generation. Production application data cannot rely on a
runtime with known container-materialization corruption.

**Required change:** make this a toolchain release blocker, add minimized regression tests, run
sanitizer builds where possible, and remove workaround-only acceptance as a production criterion.

#### P0-F — Public TLS/HTTP2 exposure is premature

The TLS handshake is performed synchronously in the accept path in the reviewed worker, which can
stall a worker. HTTP/2/h2c also needs exact-preface, frame, stream, HPACK, and resource-limit
conformance.

**Deployment rule until fixed:**

```text
Internet
  -> CDN/WAF/reverse proxy (TLS, HTTP/2, request limits)
  -> private HTTP/1.1 or Unix socket
  -> Simple application server
```

Disable direct public TLS/H2 in the Simple server until async handshake timeouts, nonblocking
handshakes, fuzzing, and interoperability suites pass.

### 3.2 Additional hardening requirements

- Reject duplicate/conflicting `Content-Length` and `Transfer-Encoding` ambiguity.
- Strictly validate request method, target, version, header names, and control bytes.
- Absolute header deadline plus minimum data rate, not only idle timeout.
- Per-IP, per-tenant, per-route, and sensitive-business-flow rate limits.
- Connection, TLS-handshake, concurrent-stream, and pending-write caps.
- Authentication middleware enabled by default for non-public routes.
- CORS allowlists; CSRF protection for cookie sessions; secure cookie policy.
- Security headers and content-type correctness.
- Request ID, trace context, actor/tenant context, structured access and security logs.
- Graceful shutdown, drain, worker restart, and listener-failure system tests.
- Fuzz suites for HTTP/1 parsing, chunk framing, path decoding, HTTP/2 frames/HPACK, TLS records,
  multipart, range requests, and proxy behavior.
- Request-smuggling differential tests against the selected edge proxy.

### 3.3 Web-server acceptance gate

The Simple server may become an internet-facing ERP application server only after:

1. shared sync/async protocol-core parity;
2. all P0 findings closed;
3. native codegen regression fixed;
4. parser/path/TLS/H2 fuzz corpus stable;
5. edge differential tests pass;
6. dynamic handler and security-context end-to-end tests pass;
7. load, slow-client, partial-I/O, and graceful-drain tests pass;
8. security review against OWASP ASVS and API Security requirements.

---

## 4. Database and persistence decision

### 4.1 Current state

The repository documentation distinguishes:

- a lightweight embedded SDN/file database;
- a historical full MVCC/WAL server that is unfinished and absent from the active worktree;
- a very small SimpleOS in-memory service with bounded tables/rows and basic create/insert/select
  behavior;
- a planned PostgreSQL/libSQL abstraction whose feature table still marks the drivers, pooling,
  transactions, mapping, and introspection as planned.

A SQLite runtime binding and Simple wrapper do exist. They support open/close, basic execution,
prepared statements, typed binds, queries, and transaction calls. This is a useful seed for
local/offline device storage, but it is not yet a production synchronization subsystem.

### 4.2 Production source of truth

Use a currently supported PostgreSQL release as the authoritative store for the first production
package.

Recommended topology:

```text
Application instances
  -> connection pool
  -> PostgreSQL primary
       -> standby/read replica
       -> WAL archive + point-in-time recovery
       -> encrypted backup repository

Transactional outbox
  -> workers/connectors/notifications/analytics
```

### 4.3 Database rules

- One database cluster and modular schemas initially; avoid database-per-microservice complexity.
- Every tenant-owned table has `tenant_id` and a database-enforced tenant policy.
- Application roles do not own tables and cannot bypass tenant policies.
- Use server-set tenant context; never trust a client-supplied tenant ID as authority.
- Financial and stock postings are append-only and balanced by constraints/tests.
- Commands use idempotency keys backed by unique constraints.
- Booking conflicts are prevented at the database level using time ranges/exclusion constraints or
  equivalent serializable locking.
- Use optimistic versions for normal aggregates and explicit row/advisory locks for scarce resources.
- Put domain mutation and outbox insertion in the same transaction.
- Use expand → migrate/backfill → contract schema changes.
- Restore drills and reconciliation are release gates, not operational follow-up.
- Partition only proven high-volume tables such as audit/outbox/ledger after measurements.
- Analytics reads use replicas or a separate warehouse; they do not run uncontrolled on the primary.

### 4.4 SQLite/offline role

Use SQLite only for bounded edge cases:

- retail POS offline queue/cache;
- restaurant table tablet menu snapshot and pending commands;
- KDS local continuity;
- developer/demo mode.

Before that use is admitted, add:

- schema migration/version table;
- WAL and busy-timeout policy;
- foreign keys enabled and verified;
- prepared-statement-only application repositories;
- typed row mapping instead of all-text convenience reads;
- encrypted credential/token storage;
- crash/power-loss and disk-full fault injection;
- operation journal with idempotent replay;
- sync cursor, conflict policy, and server reconciliation;
- bounded storage/compaction;
- corruption detection and reset/re-provision procedure.

### 4.5 Simple DB research track

Do not put finance, payroll, customer PII, stock truth, or payment state on Simple DB until it
demonstrates:

- ACID and fsync semantics;
- crash recovery under power-loss injection;
- MVCC or equivalent concurrency correctness;
- WAL checksums and corruption detection;
- transactional DDL/migrations;
- authentication, authorization, encryption, and audit;
- online backup, PITR, and restore drills;
- connection management and cancellation;
- query correctness and planner coverage;
- replication/failover or a documented single-node durability envelope;
- multi-process stress tests and production observability;
- compatibility tests against PostgreSQL-backed repository contracts.

The enterprise package should depend on a repository/transaction interface, allowing Simple DB to
become a future adapter without blocking product delivery.

---

## 5. Target product architecture

### 5.1 Product name and boundary

Use **Simple Enterprise Suite (SES)** as the product name while preserving the existing
**Unified Business Suite (UBS)** terminology for the internal MDSOC+ architecture.

Suggested product repository:

```text
simple-enterprise/
  app/
    api/
    worker/
    web/
    pos/
    table_order/
    kitchen_display/
    admin/
  src/
    foundation/
    party/
    catalog/
    pricing/
    crm/
    sales/
    inventory/
    procurement/
    finance/
    booking/
    rental/
    restaurant/
    hcm/
    channels/
    support/
    analytics/
  api/
  schema/
  migrations/
  config/
  test/
    unit/
    integration/
    contract/
    system/
    recovery/
    security/
    performance/
  doc/
    adr/
    runbook/
    country_pack/
```

Pin the `simple` toolchain/platform dependency to an admitted commit. The main monorepo keeps only a
small example/smoke test that proves compatibility.

### 5.2 Runtime architecture

```text
Customer Web/PWA      POS/Kiosk       Table Tablet       Employee/Admin       External Channels
       |                   |                |                    |                     |
       +-------------------+----------------+--------------------+---------------------+
                                           |
                                 CDN/WAF / Edge Proxy
                                           |
                              Identity / API Gateway Policy
                                           |
              +----------------------------+-----------------------------+
              |             Simple modular application                   |
              | Foundation | CRM | Sales | Inventory | Finance | HCM      |
              | Commerce | Booking/Rental | Restaurant | Channel Hub      |
              +----------------------------+-----------------------------+
                                           |
                       PostgreSQL transaction + transactional outbox
                                           |
                    +----------------------+------------------------+
                    |                      |                        |
                 Workers             Device gateway          Connector workers
          notifications/documents   live table/KDS state   Amazon/other channels
                    |                      |                        |
                Object store            Redis*             External APIs/queues
                                           |
                                 Analytics/search pipeline

* Redis is optional and never the source of truth.
```

### 5.3 Why modular monolith first

The domains require strong cross-module transactions:

- order + stock reservation + payment state + outbox;
- restaurant bill + payment + stock recipe consumption + accounting posting;
- rental return + damage fee + deposit refund + asset status;
- marketplace order + internal order + stock allocation.

A modular monolith preserves these transactions while allowing strict module ownership. Extract a
module only when there is measured scaling, isolation, or release-independence value.

### 5.4 Shared foundation

All modules consume, but do not redefine:

- Tenant, legal entity, business unit, location, cost center;
- Party, person, organization, customer, supplier, employee link;
- Money, currency, exchange rate, tax class, unit of measure;
- Identity, session, device identity, role, permission, attribute policy;
- Document number, status transition, approval, attachment, comment;
- Audit event, idempotency, optimistic version, request/trace context;
- Repository, unit of work, transaction, outbox, clock, sequence;
- Notification, template, localization, retention, privacy request.

---

## 6. Enterprise module package

### 6.1 Foundation and governance

- multi-company/multi-tenant organization model;
- users, employees, devices, service accounts;
- RBAC plus tenant/location/ownership attributes;
- approvals, delegation, segregation of duties;
- audit, retention, legal hold, privacy requests;
- workflow/status engine;
- document templates and numbering;
- configuration and feature flags;
- localization/country packs.

### 6.2 CRM and sales

- lead, account, contact, activity, campaign source;
- opportunity/deal pipeline and forecast;
- tasks, calls, email/message timeline;
- quotation, version, discount approval, contract;
- sales order, fulfillment, invoice request, return;
- customer credit, price list, sales territory, commission;
- customer portal and service handoff.

### 6.3 Finance and accounting

- chart of accounts and accounting dimensions;
- journal, balanced entries, period close and lock;
- accounts receivable/payable;
- invoice, credit/debit note, payment allocation;
- bank statement import and reconciliation;
- taxes, withholding, multi-currency, exchange revaluation;
- budgets, assets, depreciation;
- settlement reconciliation for POS/payment/marketplace channels;
- immutable audit and posting provenance.

Country-specific filing, e-tax invoice, payroll, and labor rules must be isolated in reviewed
country packs rather than embedded in generic core logic.

### 6.4 Product, pricing, inventory, procurement

- product template, variant, SKU, barcode, UOM, bundle, service;
- menus and recipes reference product/SKU records;
- price lists, customer/channel prices, promotions, coupons;
- warehouse, zone, bin, lot, serial, expiry;
- immutable stock ledger and stock reservation;
- transfer, adjustment, cycle count, picking/packing/shipping;
- supplier, requisition, RFQ, quotation, purchase order, receipt;
- purchase invoice and landed cost;
- replenishment and reorder rules.

### 6.5 HR/HCM/payroll

- organization, position, employee, employment contract;
- recruitment and onboarding/offboarding;
- shift, attendance, time entry, overtime, leave;
- performance, training, asset assignment, expense;
- payroll input, calculation trace, payslip, deduction, journal export;
- employee self-service and manager approvals.

For Korea, payroll and labor support must be a versioned country pack with effective-dated rules,
calculation explanations, statutory form outputs, and external review. The core should first deliver
employee/contract/time/leave data and integrate with an established payroll service before claiming
full payroll correctness.

### 6.6 Support, projects, documents, analytics

- ticket/case, SLA, assignment, escalation;
- project, task, time, expense, billing;
- document storage, templates, signatures, retention;
- operational dashboards, financial reports, audit reports;
- analytics export/warehouse;
- AI assistance only through scoped, approved commands with evidence and audit.

---

## 7. Unified store application

The store product is not a separate accounting island. It is an operational front end over the same
product, party, price, stock, order, payment, and accounting cores.

### 7.1 User applications

| Application | Primary users | Core capabilities |
|---|---|---|
| Customer web/PWA | shoppers/guests | browse, cart, booking, reservation, order, payment, receipt, cancel/return |
| Retail POS | cashier/store employee | barcode, cart, discounts, customer, payment, return, offline queue, shift close |
| Self-order kiosk | customer | menu/catalog, modifiers, table/pickup, payment, order status |
| Table tablet | seated customer | table-bound menu, add order, request staff, split/request bill, language/accessibility |
| Waiter screen | floor staff | floor/table status, open table, order, transfer/merge, serve, payment handoff |
| Kitchen display | kitchen/bar | station tickets, courses, priority, timing, ready/recall/cancel |
| Rental/booking desk | employee | availability, hold, check-in/out, deposit, damage, extension, maintenance |
| Warehouse/fulfillment | operators | reserve, pick, pack, ship, receive, count |
| Manager/admin | owner/manager | catalog, menu, price, staff, floor/seat maps, stock, reports, configuration |
| Enterprise back office | finance/HR/CRM/procurement | accounting, employee, customer, supplier, purchasing, reconciliation |

### 7.2 Goods-selling workflow

```text
Catalog/price/tax
 -> cart or quotation
 -> stock availability and reservation
 -> payment authorization/capture
 -> sales order
 -> fulfillment/pickup/shipping
 -> stock movement
 -> invoice/receipt and accounting posting
 -> return/refund/credit note when required
```

Rules:

- order state is separate from payment and fulfillment state;
- stock is reserved before commitment and released on timeout/cancel;
- every retry has an idempotency key;
- payment webhooks are verified, deduplicated, and reconciled;
- promotions are deterministic and explainable;
- POS close reconciles expected cash/card/channel totals to actual settlements.

### 7.3 Rental rooms, video rooms, equipment, and seats

Use one `ReservableResource` abstraction with distinct policies:

| Resource mode | Example | Conflict rule |
|---|---|---|
| Exclusive unit | room, studio, equipment | one booking per time range |
| Capacity pool | shared room/session | total booked quantity ≤ capacity |
| Assigned seat | theater/video room/desk | selected seat unavailable in overlapping session |
| Flexible area | restaurant table set | allocation can merge/split resources under policy |

Core entities:

- resource type, resource unit/group, venue, seat-map version;
- availability calendar, opening hours, blackout, maintenance;
- rate plan, duration band, peak/off-peak price, promotion;
- hold with TTL, booking, guest/customer, participant count;
- deposit, cancellation policy, no-show, waitlist;
- check-in, usage, extension, check-out;
- damage/overage/fine, refund, maintenance/cleaning buffer.

Concurrency correctness:

- database constraint or serializable lock prevents overlap;
- hold expiration is server-time based;
- seat-map version is pinned to a session;
- payment and booking confirmation use a saga only when the payment provider cannot participate in
  the transaction;
- reconciliation detects paid-but-unconfirmed and confirmed-but-unpaid edge cases.

### 7.4 Restaurant reservation and table ordering

Core model:

- venue, floor, table, seat, section;
- reservation, party, waitlist, arrival, seating;
- table session and table-bound device session;
- menu, menu version, category, item, combo;
- modifier group/option, required count, allergen/tag;
- order, line, course, service type;
- kitchen station, preparation ticket, item status;
- bill, split, discount, service charge/tip, payment/refund;
- recipe/BOM and stock consumption;
- takeout, pickup, delivery-channel order.

#### Korea-style table tablet

Each physical tablet must be a managed device, not merely a browser with a table number in a URL.

- provisioned device identity/certificate;
- explicit tenant/location/table assignment;
- locked-down kiosk mode and remote revoke;
- signed configuration/menu snapshot;
- Korean/English and accessibility support;
- sold-out/price/menu-version push;
- local pending-command journal for network interruption;
- idempotent add/update/cancel commands;
- heartbeat and stale-device alert;
- staff-call and bill-request events;
- no storage of raw card data;
- automatic session reset after table close.

#### Restaurant operational flow

```text
Reservation or walk-in
 -> table/party session
 -> menu snapshot
 -> customer/waiter adds items and modifiers
 -> validation and price snapshot
 -> route each line to kitchen/bar station
 -> prepare -> ready -> served
 -> additional rounds/courses
 -> transfer/merge/split when needed
 -> bill and payment
 -> close table
 -> consume recipe stock and post accounting
```

The first competitive baseline should include floor plans, live table state, booking, kitchen
notifications/display, order transfer/merge, courses, bill split, self-ordering, and temporary
network-outage continuity.

---

## 8. External marketplace and web-store integration

### 8.1 Channel Hub architecture

Do not put Amazon-specific fields or calls inside sales/inventory modules. Use a canonical connector
boundary:

```text
Core Product/Inventory/Order/Finance
          |
      Channel Hub
          |
  +-------+--------+---------+
  |                |         |
Amazon adapter  Korea adapter  Other web-store adapter
```

Canonical operations:

- authorize/revoke channel account;
- import catalog/product types;
- create/update listing;
- update price and available quantity;
- receive/import order;
- acknowledge/accept order;
- publish fulfillment/tracking/cancellation;
- receive return/refund;
- import fees, settlements, and payouts;
- reconcile channel state against internal state.

### 8.2 Connector runtime requirements

- OAuth/token vault and least-privilege scopes;
- credential isolation per tenant/channel;
- notification/webhook inbox storing raw signed payload metadata;
- deduplication by provider event/message ID;
- cursor/checkpoint for pull APIs;
- per-operation token bucket and adaptive throttling;
- exponential backoff with jitter and retry classification;
- dead-letter queue and operator replay;
- immutable request/response audit with PII redaction;
- provider-specific mapping/versioning;
- periodic full reconciliation, never notification-only trust;
- settlement/fee mapping into finance;
- contract tests using provider sandbox plus recorded fixtures;
- kill switch per tenant, connector, and operation.

Amazon SP-API exposes distinct catalog, listing, pricing, order, shipping/fulfillment, reports,
feeds, and notification workflows and enforces operation-specific rate limits. Therefore the adapter
must be asynchronous, rate-aware, checkpointed, and reconciliation-driven rather than a synchronous
passthrough from a user request.

### 8.3 Channel rollout order

1. Generic adapter SPI and mock channel.
2. Amazon private-application integration for one pilot seller.
3. One Korean channel selected by the pilot business.
4. Shopify or another general web-store connector.
5. Additional channels only after canonical mapping and reconciliation are stable.

---

## 9. API, command, and event contracts

### 9.1 Command envelope

Every external mutation uses a server-established context:

```text
CommandEnvelope
  request_id
  idempotency_key
  actor_id
  tenant_id            # injected/validated by server, not trusted from payload
  location_id
  expected_version?
  occurred_at_client?
  received_at_server
  trace_context
  payload
```

### 9.2 External APIs

- REST/JSON for normal web/admin/POS commands and queries;
- WebSocket or SSE for table/KDS/order-status updates;
- provider webhooks/notifications through a dedicated ingress;
- bulk import/export through asynchronous jobs;
- versioned schemas generated from the canonical data specification;
- field-level authorization and response filtering;
- cursor pagination and stable sorting;
- machine-readable error codes with safe human messages.

### 9.3 Domain and integration events

Examples:

- `sales.order.created`
- `inventory.stock.reserved`
- `payment.authorized`
- `booking.hold.created`
- `booking.confirmed`
- `restaurant.ticket.sent`
- `restaurant.item.ready`
- `channel.order.received`
- `finance.journal.posted`

Delivery may be at least once; business effects must be exactly once through unique keys and
idempotent handlers.

### 9.4 Source-of-truth rules

- Party owns customer/supplier/person identity.
- Catalog owns product/SKU/menu-linked product definitions.
- Pricing owns price snapshots and promotion decisions.
- Inventory owns availability, reservations, and stock ledger.
- Sales owns commercial orders.
- Booking owns time/resource allocation.
- Restaurant owns table session and preparation state.
- Payments own provider transaction state, while Finance owns accounting settlement.
- Finance owns posted journals and periods.
- Channel Hub owns external IDs and synchronization state, never internal business truth.

---

## 10. Security, privacy, and compliance architecture

### 10.1 Identity and authorization

- OIDC/OAuth-based workforce/customer identity integration;
- MFA for privileged roles;
- short-lived sessions, revocation, device binding where appropriate;
- RBAC plus tenant, legal entity, location, ownership, amount, and shift attributes;
- segregation of duties for refunds, price overrides, journal posting, payroll, and user
  administration;
- service accounts and devices have narrower permissions than humans;
- every object and function access is authorized server-side.

### 10.2 Payment scope

- prefer hosted payment pages/fields or certified terminals;
- store provider tokens and masked references, not raw PAN/CVV;
- isolate payment webhooks and terminal/device credentials;
- verify signatures and reconcile independently;
- design and assess against PCI DSS v4.0.1 according to the selected payment architecture.

### 10.3 Korean deployment pack

A Korean country pack should include reviewed requirements for:

- personal-data purpose, retention, deletion, access, and breach operations;
- employee/payroll records and explainable payslip calculations;
- VAT/tax invoice integration and accounting mappings;
- payment terminal and receipt integrations;
- Korean address, phone, name, currency, locale, and business identifiers.

This is a product and legal/compliance workstream, not only a translation task. Rules must be
effective-dated and independently testable.

### 10.4 Assurance baseline

- OWASP ASVS 5.0 target, at least Level 2-equivalent controls for the SaaS application;
- OWASP API Security threat cases, especially object/function authorization, resource exhaustion,
  sensitive business-flow automation, SSRF, inventory, and unsafe third-party API consumption;
- dependency/SBOM scanning, secret scanning, SAST, DAST, fuzzing;
- tenant-isolation and privilege-matrix tests;
- payment/refund/fraud-abuse controls;
- immutable security audit and alerting;
- periodic penetration and recovery review.

---

## 11. Observability and operations

Use one correlation model across HTTP, commands, database transactions, outbox events, connectors,
and device sessions:

- request/trace ID;
- tenant/location;
- actor/device/service identity;
- command/idempotency key;
- order/booking/payment/ticket/channel identifiers;
- sanitized error code.

Signals:

- traces for request and asynchronous flow;
- metrics for latency, error, saturation, queue age, retries, reconciliation gaps;
- structured logs for operator/security events;
- profiles only in controlled environments.

Required dashboards:

- API/service SLO;
- database pool/locks/replication/backup;
- outbox and worker lag;
- POS/table/KDS device health;
- booking conflicts/expired holds;
- payment and settlement reconciliation;
- marketplace rate limits/retries/DLQ;
- stock mismatch/negative availability;
- audit/security alerts.

Runbooks:

- payment webhook outage;
- marketplace throttling/outage;
- POS offline recovery;
- table-device compromise/loss;
- database failover/PITR;
- accidental price/menu publication;
- oversell/reconciliation incident;
- privacy request and security incident.

---

## 12. Parallel-agent implementation plan

### 12.1 Coordination model

Use one integration owner and exclusive path ownership. Parallel agents may not edit shared contracts
directly after freeze.

Frozen contracts before broad parallel work:

1. `TenantContext`, `ActorContext`, `DeviceContext`
2. `Money`, `Quantity`, `TimeRange`, `Address`, `PartyId`, typed IDs
3. `CommandEnvelope`, `CommandResult`, `ErrorCode`
4. `DomainEvent`, `OutboxRecord`, `AuditRecord`
5. `Repository`, `UnitOfWork`, migration interface
6. authorization decision interface
7. API versioning and JSON/error conventions
8. product, order, stock-reservation, payment, and booking identity contracts
9. modern sspec fixture/contract format
10. observability field names

Shared-contract changes require an ADR, compatibility impact, migration plan, and integration-owner
merge.

### 12.2 Agent lanes

| Lane | Exclusive ownership | First outputs | Depends on | Exit evidence |
|---|---|---|---|---|
| L0 Architecture/integration | ADRs, shared contracts, dependency graph, merge train | contract v1, repo layout, module boundaries | none | contract tests and architecture review |
| L1 Toolchain/build | pinned Simple release, CI, package/build cache, local environments | reproducible build/test image | L0 | clean build, focused tests, admitted compiler; no unexplained exit 139 |
| L2 HTTP/API platform | shared HTTP core, app routing, API framework, edge config | private HTTP/1 API and hardened parser | L0/L1 | fuzz/security/system tests and dynamic dispatch proof |
| L3 Persistence/data | PostgreSQL adapter, pool, transactions, migrations, outbox, SQLite edge adapter | repository/unit-of-work implementation | L0/L1 | crash/retry/migration/restore tests |
| L4 Identity/foundation | tenant, org, party, users, roles, devices, approval, audit | foundation schema and authorization | L0/L3 | privilege matrix and cross-tenant negative tests |
| L5 Catalog/inventory/procurement | product, price, stock ledger/reservation, supplier/PO/receipt | sellable SKU and stock truth | L3/L4 | concurrent reserve/fulfill/return invariants |
| L6 CRM/sales/finance | lead/deal/quote/order/invoice/payment posting/GL MVP | quote-to-cash vertical | L3/L4/L5 | balanced journals, idempotent order/payment tests |
| L7 Booking/rental | resources, calendars, holds, seats, rental lifecycle | room/seat rental vertical | L3/L4/L6 | overlap, TTL, deposit, check-in/out scenarios |
| L8 Restaurant/device | menu/table session/order/ticket/KDS/device gateway | table-order vertical | L3/L4/L5/L6 | offline replay, kitchen routing, split/merge/payment scenarios |
| L9 Web/POS/admin UX | customer PWA, POS, waiter, KDS, employee/admin workspaces | role-specific usable flows | API contracts from L2 and domain contracts | browser/device system tests and accessibility checks |
| L10 Channel Hub | adapter SPI, inbox, throttling, mapping, reconciliation, Amazon pilot | first external channel | L3/L5/L6 | sandbox/fixture/notification/reconciliation tests |
| L11 Security/QA/SRE | threat models, test harness, observability, deployment, recovery | continuous evidence gates | all lanes | ASVS matrix, restore drill, load/fault/security reports |
| L12 HCM/country pack | employee/contract/time/leave and Korean integration boundary | HCM MVP and payroll export/integration | L3/L4/L6 | effective-dated rule tests and reviewed country-pack evidence |

### 12.3 Delivery waves

#### Wave 0 — Evidence and contract freeze

- retain existing prototype tests;
- classify example versus production code;
- pin a stable Simple compiler/runtime;
- establish product repository and CI;
- freeze contracts and schema conventions;
- add PostgreSQL and edge deployment decisions;
- create an executable architecture smoke test.

**Gate:** all agents can build and run the same test suite from a clean environment.

#### Wave 1 — Production foundation

Parallel: L2 HTTP, L3 persistence, L4 identity/foundation, L11 security/ops.

Deliver:

- private hardened API service;
- PostgreSQL transactions/migrations/outbox;
- tenant/party/identity/device/RBAC;
- audit and observability;
- backup/PITR/restore automation.

**Gate:** a durable, tenant-isolated, idempotent sample command survives restart and restore.

#### Wave 2 — Commerce kernel

Parallel: L5 catalog/inventory, L6 CRM/sales/finance, L9 initial admin/POS.

Deliver:

- product/SKU/price/tax;
- customer and CRM deal;
- cart/quote/order/payment state;
- stock reserve/fulfill/return;
- balanced accounting posting;
- cashier/admin UI.

**Gate:** one goods sale from UI to stock and journal, including retry, refund, and restore.

#### Wave 3 — Booking and restaurant verticals

Parallel: L7 booking/rental, L8 restaurant/device, L9 customer/waiter/KDS UX.

Deliver:

- room/resource/seat availability and holds;
- rental check-in/out/deposit/damage flow;
- restaurant floor/table/reservation;
- table tablet, waiter, kitchen display;
- offline command journal and reconciliation.

**Gate:** concurrent booking conflict tests and an end-to-end restaurant service under temporary
network loss.

#### Wave 4 — External channels and enterprise breadth

Parallel: L10 Amazon/channel pilot, L12 HCM/country pack, procurement/finance expansion.

Deliver:

- canonical channel mappings;
- Amazon listing/order/inventory/fulfillment/settlement pilot;
- employee/contract/time/leave;
- purchase-to-pay;
- stronger finance, tax, reconciliation, reports.

**Gate:** external order reconciles through stock, fulfillment, fees, payout, and accounting without
duplicate effects.

#### Wave 5 — Pilot and production admission

- load and soak tests;
- fault injection and chaos scenarios;
- security/tenant-isolation assessment;
- backup/restore and regional failover drills;
- data migration rehearsal;
- operational training/runbooks;
- limited tenant/location pilot;
- evidence-based go/no-go review.

### 12.4 Merge and review rules

- one worktree/branch per lane;
- small commits tied to acceptance criteria;
- no shared schema edits outside L0/L3 ownership;
- contract-first tests before implementation merge;
- lane unit tests plus cross-lane integration fixture;
- generated API/schema compatibility diff on every merge;
- migration rollback/forward evidence;
- high-model or senior-human review for auth, finance, booking concurrency, payments, and recovery;
- merge train order: contracts → platform → foundation → domain → UI/connectors → system evidence.

---

## 13. Proposed release targets

These are design targets to validate with the pilot workload:

### Correctness

- zero unbalanced posted journals;
- zero duplicate business effects under retry/replay;
- no negative available stock unless explicitly allowed;
- no overlapping exclusive bookings;
- every price/tax/discount decision reproducible from a snapshot;
- full payment/order/settlement reconciliation queue with visible unresolved items.

### Reliability

- 99.9% pilot service availability target;
- ordinary API p95 below 300 ms at admitted load;
- table-order acknowledgment below 1 second on healthy local connectivity;
- RPO no worse than 5 minutes and RTO no worse than 60 minutes for the initial hosted pilot;
- regular automated restore with periodic human-observed recovery drill;
- offline POS/table replay produces zero duplicate accepted commands.

### Security

- zero cross-tenant access in automated privilege matrix;
- MFA and separation of duties for privileged/refund/finance/payroll actions;
- no raw payment card storage;
- all external webhooks signed/verified/deduplicated;
- ASVS/API-security gate and penetration-review findings closed or explicitly risk-accepted.

### Operations

- every request/command/event is traceable by correlation ID;
- every DLQ/reconciliation item has owner, age, and replay path;
- backups, replica lag, queue lag, device health, and external-channel throttling are monitored;
- on-call runbooks are exercised before general availability.

---

## 14. Highest-priority backlog

### Immediate P0

1. Move product ownership to `simple-erp`/`simple-enterprise`; keep main-repo example thin.
2. Pin an admitted Simple compiler/runtime and close current native correctness blockers.
3. Define/freeze foundation, command, event, repository, and API contracts.
4. Implement PostgreSQL adapter, pool, transactions, migrations, and outbox.
5. Merge sync/async HTTP core and close async request-limit/path/dispatch/TLS exposure gaps.
6. Integrate live identity/tenant/device context and database-enforced isolation.
7. Replace toy durable/audit hashes with production cryptographic and database-backed records.
8. Build the first goods-sale vertical through UI → API → DB → stock → payment state → journal.

### Next P1

9. Build the shared resource/seat booking engine.
10. Build restaurant table session, menu/modifiers, kitchen tickets, and employee/KDS screens.
11. Build offline SQLite command journal and reconciliation.
12. Build Channel Hub and Amazon private pilot.
13. Add purchase-to-pay and stronger AR/AP/bank reconciliation.
14. Add HCM employee/contract/time/leave, then a reviewed Korean payroll integration/country pack.

### Explicitly defer

- a custom production Simple DB server as the ERP dependency;
- public direct Simple TLS/HTTP2 exposure;
- microservice decomposition of core transaction domains;
- universal event sourcing;
- storing raw payment card data;
- simultaneous implementation of many marketplaces;
- claiming full Korean payroll/tax compliance without reviewed country-pack evidence.

---

## 15. Evidence references

Repository paths used in this assessment include:

- `examples/12_business/simple_erp/README.md`
- `examples/12_business/simple_erp/src/framework/guarded.spl`
- `examples/12_business/simple_erp/src/kernel/durable_log.spl`
- `examples/12_business/simple_erp/src/lanes/{crm,reservation,sale,market,restaurant}.spl`
- `examples/12_business/simple_erp/src/web/{routes,dashboard}.spl`
- `examples/12_business/simple_erp/ubs_test/`
- `ormastes/simple-erp/README.md`
- `ormastes/simple-erp/doc/{architecture,production_plan,readiness_gate,agent_teams}.md`
- `src/lib/nogc_async_mut/http_server/{server,worker,parser,router,middleware,connection}.spl`
- `src/lib/nogc_sync_mut/http_server/`
- `.spipe/webserver_harden/state.md`
- `doc/07_guide/lib/database/simple_db.md`
- `doc/08_tracking/bug/simple_db_perf_native_server_blockers_2026-06-21.md`
- `src/os/services/database/simple_db_service.spl`
- `src/runtime/runtime_sqlite.c`
- `src/lib/nogc_sync_mut/io/sqlite_sffi.spl`
- `doc/09_report/misc/stdlib/db.md`

External primary documentation reviewed:

- Odoo 19 POS, self-ordering, restaurant, preparation-display, and rental documentation;
- Frappe CRM/ERPNext integration and ERPNext POS/restaurant documentation;
- Amazon Selling Partner API onboarding and notifications documentation;
- PostgreSQL row security, range/exclusion constraints, standby, and PITR documentation;
- OWASP ASVS and API Security Top 10;
- PCI Security Standards Council PCI DSS v4.0.1 documentation;
- Korean Personal Information Protection Act sources and Ministry of Employment and Labor
  payroll-statement guidance.

---

## Final recommendation

The project should not attempt to "finish all ERP modules" inside the current example. The correct
next product is a **durable modular enterprise platform with three proving verticals**:

1. **Goods sale** — catalog, inventory, payment, fulfillment, return, accounting.
2. **Resource/seat rental** — availability, hold, booking, deposit, check-in/out, damage, billing.
3. **Restaurant service** — reservation, table tablet, waiter, kitchen display, payment,
   stock/accounting.

Once these share one tenant/party/product/price/order/payment/stock/finance foundation and pass
recovery/security gates, CRM, procurement, HCM, marketplace connectors, and additional enterprise
modules can scale in parallel without becoming disconnected applications.
