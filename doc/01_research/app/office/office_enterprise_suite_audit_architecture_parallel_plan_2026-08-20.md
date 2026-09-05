# Simple Office + Enterprise Suite: Research, Architecture, and Parallel Development Plan

Date: 2026-08-20
Status: research (completed report, saved from external deep-audit session)

Companion summary: this document is the saved full report of the Office +
Enterprise Suite deep audit (1,413-line source report; 300 uniquely identified
tests; three architecture diagrams; staged delivery gates; 18 parallel-agent
lanes with exclusive file ownership and dependency ordering).

> **DB-target clarification (owner, 2026-08-20):** wherever this report says
> "PostgreSQL adapter" or "web/db server", the target is **Simple's own DB
> server** (`std.database.server` =
> `src/lib/nogc_sync_mut/database/server/{server,session,txn,capability,durability,protocol,transport}.spl`),
> not an external PostgreSQL deployment. Simple has three DB kinds (canonical
> map: `doc/07_guide/lib/database/db_implementations_map.md`): the **textual
> DB** (SDN-file store, `SdnDatabase` — also the DB server's store port), the
> **embedded DB** (in-process SQL: `database/pure_sql`, C SQLite via SFFI,
> interpreter `rt_sqlite` emulation) for local/dev/test, and the **DB server**
> as the authoritative multi-user enterprise tier. `postgres_mimic` is only a
> PostgreSQL
> compatibility surface on top, not the server itself. All "PostgreSQL"
> capabilities named below (ordered typed queries, transactions, unique
> idempotency keys, RLS, non-overlap constraints, CAS locking, outbox
> claiming) are requirements on the Simple DB server.

## Main audit verdict

`simple` already has a substantial implementation base:

- Office exposes Writer, Calc, Slides, Base/database, Draw, Math, Mail,
  Planner, publishing, format conversion, formulas, charts, pivots, queries,
  mail merge, notes, and an ERP bridge. This is real functionality rather than
  only design documentation.
- Enterprise contains many concrete modules, including sales, CRM, finance,
  GL, FX, tax, pricing, payment, procurement, inventory, manufacturing,
  fulfillment, returns, subscriptions, HCM, booking, restaurant, loyalty,
  notifications, channels, sessions, outbox, and the enterprise store.
- Many newer enterprise modules have good local invariants: append-only event
  rows, integer monetary arithmetic, explicit transitions, idempotency, audit,
  outbox, and tenant filtering. Inventory and manufacturing, for example, are
  deliberately small but real vertical slices.

However, it is currently a collection of broad Office foundations and focused
enterprise verticals, not yet one integrated production suite.

## Highest-priority findings

1. **Do not build a separate web Office application.**
   The existing Simple IDE/editor should become the common workbench for IDE,
   Office, and enterprise profiles. The current IDE entry point primarily
   reports capabilities/readiness, while the editor launcher supports GUI, SDL
   GUI, and TUI but not a browser workbench.

2. **The existing Calc access server must remain a test protocol.**
   It is explicitly a semantic testing/debugging surface rather than a general
   Office hosting protocol. It lacks document authorization, versions, locks,
   browser sessions, storage, collaboration, and multi-document lifecycle.

3. **Replace CSV-style ERP integration with a typed Enterprise Data View
   contract.** The current bridge has a fixed sales schema and a lightweight
   CSV/ubslog path. It cannot safely express arbitrary enterprise entities,
   paging, typed fields, provenance, policy, deltas, aggregates, or writeback
   conflicts.

   The report defines an EDV contract supporting:
   - Typed schemas and stable semantic field IDs
   - Server-side filtering, sorting, aggregation, paging, and delta refresh
   - Row and field authorization
   - Snapshot IDs, source revisions, ETags, freshness, and provenance
   - Calc live tables
   - Writer scalar and repeating-section bindings
   - Slides KPI, table, and chart bindings
   - Draft-only ChangeSets with optimistic concurrency
   - External OData adaptation without making OData the internal domain model

   OData is appropriate for an external typed query adapter, while WOPI
   provides the appropriate file-host interoperability boundary for metadata,
   file access, updates, and locks.

4. **Correct accounting before adding more ERP breadth.**
   Procurement currently inserts journal rows directly, bypassing the finance
   period-aware posting seam. In addition, `enterprise_finance` and
   `enterprise_gl` maintain separate journal and `gl_lines` accounting models.
   This creates a closed-period bypass and a potential split accounting system
   of record.

   The first corrective gate therefore requires:
   - One canonical journal service
   - No raw business-module journal insertion
   - Migration and reconciliation of both current ledgers
   - Period, source-document, currency, dimensions, reversal, and
     posting-state support
   - A static architecture test rejecting accounting writes outside the
     canonical repository

5. **Implement the production PostgreSQL adapter and explicit event
   ordering.** The store documents that interpreter SQLite is non-ACID, does
   not enforce constraints correctly, and ignores predicate semantics. It also
   reads complete tables without an ORDER BY, while several modules interpret
   the last encountered row as the current state or effective rate. That is
   both an O(N) scalability limit and a deterministic-correctness risk on a
   real SQL engine.

   The target PostgreSQL adapter includes typed ordered queries, indexes,
   paging, transactions, unique idempotency keys, row-level security,
   non-overlap constraints, compare-and-swap locking, outbox claiming, and
   migration reconciliation. PostgreSQL RLS supplies useful defense in depth,
   but domain and field policy must still be enforced above the database.

6. **Centralize authorization.**
   Several modules reuse unrelated procurement or sales actions, while GL,
   tax, pricing, returns, and subscriptions define local authorization
   functions. This preserves isolated module tests but prevents global
   least-privilege analysis and reliable Office writeback authorization.

7. **Replace the current collaboration helper rather than exposing it over
   HTTP.** Calc coauthoring currently uses per-cell revisions and
   merge-order-sensitive last-writer-wins behavior. The target design adds
   authenticated document sessions, durable operations, causal metadata,
   presence separation, snapshots, compaction, offline queues, and explicit
   same-cell conflicts.

## Browser IDE design

The proposed architecture preserves the repository's existing plugin
direction — manifests, contribution points, lazy activation, scoped dependency
injection, capabilities, and constrained AOP — but makes it executable.

It introduces:

```
simple ide --web --workspace <path> --open <uri>
simple office --web writer <document>
simple office --web calc <workbook>
simple office --web slides <deck>
simple enterprise --web --module crm --tenant <tenant>
```

Plugin options use namespaced forwarding such as `--x-office-...` and
`--x-enterprise-...`, allowing new capsule options without modifying or
rebuilding the core CLI parser.

Browser-safe extensions execute in a worker; filesystem, process, terminal,
compiler, debugger, Git, and similar privileged functions remain in a
remote/native workspace host. This follows the same fundamental host
separation used by web-capable editor extension architectures.

## Test and implementation plan

The artifact includes exactly 300 named cases, organized into 20 groups:

- Architecture and plugins
- Browser launch and bootstrap
- Identity, tenancy, and policy
- Document repository and WOPI
- Writer, Calc, Slides, and auxiliary Office apps
- Collaboration and offline operation
- EDV bindings and writeback
- Finance, CRM, SCM, manufacturing, and HCM
- OOXML/ODF/PDF interoperability
- Accessibility and localization
- Security
- Performance and concurrency
- Reliability, migrations, observability, backup, and disaster recovery

Execution follows the requested order: system SSpec first, integration second,
unit/property/fuzz third. Semantic UI state and action history are primary
evidence; screenshots supplement visual requirements.

The recommended first integrated vertical is:

> CRM opportunity → Calc quote model → Writer proposal → approval → sales order

That slice proves the common workbench, documents, EDV, policy, workflow,
writeback, collaboration, Office formats, CRM/sales integration, audit, and
end-to-end traceability without prematurely expanding every domain.

---

## Executive assessment

The repository is not an empty prototype. It already contains a broad Office
implementation surface: Writer, Calc, Impress, Mail, Planner, Notes,
Publisher, database/reporting, Math, charting, pivot tables, formula
evaluation, Markdown editing, and OOXML/ODF conversion. However, those
components are not yet assembled into a production-grade, web-launchable
collaborative suite. The current Office launcher exposes only Word, Sheets,
Slides, Mail, Planner, and Counter, while another compatibility module labels
Writer, Calc, Impress, Draw, Base, and Math as fully implemented. That binary
`implemented: true` status overstates the evidence available today.

The enterprise side has also advanced substantially. The repository contains
an enterprise storage abstraction, hardened HTTP parsing, guarded business
mutations, transactional-outbox and audit-chain concepts, and domain kernels
for CRM, finance, inventory, manufacturing, HCM, procurement, booking,
restaurant operations, and other areas. Nevertheless, many modules are bounded
kernels or probes rather than complete user-facing products. The repository's
own progress records still identify native ACID verification, self-hosted
execution, cross-runtime evidence, and full web routing as unresolved gates.

The largest missing element is therefore not another collection of independent
Office or ERP classes. It is a shared product architecture connecting:

```
Simple Workbench
    ├── Office editors
    ├── Enterprise applications
    ├── document storage and versioning
    ├── enterprise data bindings
    ├── identity and authorization
    ├── collaboration and review
    └── browser, desktop, TUI, and Simple OS runtimes
```

The recommended first integrated release is one complete vertical flow:

```
CRM lead
  → qualified opportunity
  → governed pipeline data in Calc
  → quotation generated in Writer
  → browser save and version history
  → DOCX/PDF export
  → enterprise audit record
```

That flow forces every major layer to work together and will reveal more real
defects than adding ten more disconnected enterprise modules.

---

## 1. Repository findings

### 1.1 Office has broad source coverage but incomplete product assembly

The Office module already imports:

- Word, Sheets, and Slides.
- Mail, Planner, Counter, Notes, Publisher, and database functionality.
- Chart, pivot, conditional-formatting, validation, formula, undo/redo, and
  GUI components.
- Markdown WYSIWYG.
- CSV, OOXML, and ODF import/export.
- ERP bridge functionality.

The strongest areas appear to be the underlying data models, formula engine,
format conversion, and individual feature specifications. The Office progress
records describe a large formula engine and many formula specifications, but
also state that parts of the historical pass evidence were not freshly
executable with the self-hosted native runtime.

The current public launcher is much narrower than the source inventory. It
provides cards for Word, Sheets, Slides, Mail, Planner, Counter, recent files,
and the suite UI. Base, Draw, Math, Notes, Publisher, and other capabilities
are not represented consistently in the user-facing catalog.

**Required correction**

Replace Boolean capability declarations such as `implemented: true` with an
evidence-bearing maturity model:

```
declared
source_complete
unit_verified
integration_verified
web_e2e_verified
native_verified
production_ready
```

Each capability should contain:

```
status
source_revision
test_receipt
verified_platforms
known_limitations
last_verified_at
```

This prevents a compatibility facade or source path from being presented as a
finished application.

**Naming concern**

The repository currently declares a suite named LibreOffice. "LibreOffice" and
"The Document Foundation" are registered trademarks, so the product and plugin
identifiers should use Simple Office, Simple Writer, Simple Calc, and similar
names unless explicit trademark authorization exists. Compatibility adapters
can still be named internally after the supported format or protocol.

### 1.2 The IDE is not yet the real application shell

`src/app/ide/main.spl` currently parses options and prints feature or
readiness messages. It does not enter a persistent GUI, browser, or TUI
workbench. By contrast, `src/app/editor/main.spl` constructs an editing
session and calls the actual GUI, SDL, or TUI runner.

This creates an architectural inversion:

```
Current:
IDE façade → readiness output
Editor app → actual application shell
Office app → separate GUI implementation
Enterprise web → separate server-rendered application
```

It should become:

```
Target:
Simple Workbench → actual shared shell
    ├── Code editor provider
    ├── Writer provider
    ├── Calc provider
    ├── Slides provider
    ├── Database provider
    ├── Enterprise view providers
    └── Test/debug/admin providers
```

The IDE should cease being a readiness reporter and become the common
composition root.

### 1.3 CRM exists, but only as a domain kernel

The current CRM library implements a useful minimal state machine:

```
lead
  → qualify
  → opportunity
  → won | lost
```

It includes guarded actions, tenant scoping, stage transitions, and pipeline
summaries. That is a good domain kernel, but it is not yet a complete CRM
product. It lacks the surrounding customer, communication, activity,
quotation, forecasting, and service capabilities expected from a practical
CRM.

The current enterprise web application imports routes for authentication,
booking, restaurant, HCM, procurement, finance, dashboard, catalog, order,
payment, and receipt handling. CRM is not yet exposed as a comparable
first-class workbench or web route family.

Modern integrated suites treat CRM as the start of a larger transaction chain.
Odoo connects leads, opportunities, activities, quotations, sales, inventory,
invoicing, and forecasting; ERPNext similarly connects leads and opportunities
to quotations and the selling cycle.

### 1.4 The existing ERP bridge is not a general integration layer

`erp_bridge.spl` is currently centered on converting an older ubslog sales
representation into CSV, JSON, invoices, or analytical workbook output. Its
documented V1 boundary is sales rows; it does not cover customers, inventory,
invoices, payments, tax, GL, or controlled write-back.

It should not be extended by adding more format-specific parsers. It should be
replaced or wrapped by a general, versioned Enterprise Data Binding SDK.

The legacy bridge may remain as one adapter:

```
Legacy ubslog adapter
    ↓
Enterprise Data Binding SDK
    ↓
Office bindings, reports, exports, and commands
```

### 1.5 Testing is broad at lower levels but shallow at the product boundary

The headline Office suite receipt reports 17 passed tests with zero failures
and a recorded duration of zero milliseconds. Its specification mainly checks
command dispatch, root IDs, sample data, and basic editing or formatting
behavior. There are many more specialized formula and feature tests elsewhere,
so the Office implementation should not be evaluated from the number 17 alone.
However, only a small product-level system-test surface is visible under the
Office system-test directory, and the repository's own state records say live
CLI/TUI/UI evidence remained blocked because the deployed binary was not the
required self-hosted native runtime.

The browser renderer recently achieved exact layout alignment for one selected
Office WYSIWYG fixture across Simple, Chromium, and WebKit, but the same
record notes residual glyph differences and additional unresolved layout
behavior. That is valuable regression evidence, not proof of general
Office-web fidelity.

---

## 2. Missing feature map

Priorities:

- P0: needed for the first credible integrated release.
- P1: needed for an SMB production pilot.
- P2: broader enterprise-suite competitiveness.

### 2.1 Shared Office platform

| Priority | Missing capability | Required behavior |
|---|---|---|
| P0 | Document service | Stable document IDs, object storage, metadata, content hashes, version keys |
| P0 | Autosave and recovery | Journaled changes, crash recovery, save status, conflict handling |
| P0 | Sharing and permissions | Owner, editor, commenter, viewer, link policy, expiry |
| P0 | Version history | Named versions, restore, compare, provenance |
| P0 | Browser session protocol | Open, read, save, lock, unlock, refresh lock, conflict response |
| P0 | Enterprise data bindings | Governed data sources, snapshots, refresh, lineage, explicit write-back |
| P0 | Search | Filename, metadata, document content, enterprise references |
| P1 | Comments and mentions | Threaded comments, resolution, notifications, anchors |
| P1 | Coauthoring and presence | Cursors, selections, participants, concurrent merge |
| P1 | Offline operation | Local snapshot, queued changes, reconnect and conflict handling |
| P1 | Templates | Organization templates, classifications, approved fields and branding |
| P1 | Retention and DLP | Retention schedules, legal hold, export controls, watermarking |
| P1 | Accessibility | Screen-reader semantics, full keyboard support, focus handling |
| P2 | Extension marketplace | Signed plugins, permissions, compatibility and revocation |
| P2 | Integrated e-signature | Signing workflows, certificates, audit evidence |

### 2.2 Writer

P0

- Real page model: page size, orientation, margins, sections, columns.
- Headers, footers, page numbers, page breaks, and section breaks.
- Editable tables with row/column operations, merged cells, borders, and sizing.
- Image placement, wrapping, anchoring, and captions.
- Paragraph and character style hierarchy.
- Search/replace across structural content.
- Print layout and deterministic PDF export.
- Enterprise content controls and repeated sections.
- DOCX and ODT round-trip preservation tests.

P1

- Track changes and accept/reject operations.
- Threaded comments and mentions.
- Footnotes, endnotes, citations, bibliography, cross-references.
- Fields, table of contents, indexes, captions, equations.
- Forms and protected fields.
- Spell checking, dictionaries, grammar adapters.
- Compare and merge documents.
- Accessibility metadata and document checker.

P2

- Master documents.
- Advanced publishing and mail merge.
- Legal-document numbering and clause libraries.
- AI-assisted drafting with provenance and policy controls.

### 2.3 Calc

P0

- Workbook and multi-sheet lifecycle.
- Stable dependency graph and deterministic recalculation.
- Structured tables, named ranges, named formulas.
- Sort, filter, grouping, freeze panes, data validation.
- External enterprise data source definitions.
- Refreshable data tables and immutable snapshots.
- Pivot tables and charts bound to enterprise data.
- Formula, date, locale, and error compatibility corpus.
- XLSX and ODS round-trip preservation.

P1

- Protected ranges and workbook permissions.
- Comments, notes, collaborative selection and conflict behavior.
- Query transformation pipeline.
- Scenario manager, goal seek, solver, and sensitivity analysis.
- Data lineage and cell-level provenance.
- Audit mode showing formula dependencies and enterprise origins.
- Large-workbook streaming and partial loading.
- Sandboxed custom functions.

P2

- Semantic enterprise entities as cell values.
- Data models joining multiple governed sources.
- Scheduled refresh and report distribution.
- Statistical and financial analytical packs.

Google Connected Sheets demonstrates the useful model: a sheet contains a
scoped data-source object from which tables, pivots, charts, and formulas can
be created and refreshed. Excel similarly supports richer custom data types
and workbook sessions. Simple should adopt the architectural pattern while
retaining its own API and security model.

### 2.4 Slides

P0

- Master slides, themes, layouts, and placeholders.
- Image, chart, table, shape, and text placement.
- Speaker notes and presenter mode.
- PDF and PPTX export with fidelity checks.
- Linked enterprise charts and KPI cards.
- Browser full-screen presentation.

P1

- Transitions and animations.
- Media embedding.
- Comments and collaborative editing.
- Diagram and organization-chart components.
- Accessibility order and alternative text.
- Template governance and corporate branding.

P2

- Live audience interaction.
- Recorded narration.
- Data-driven presentation generation.

### 2.5 Other Office applications

The following should become first-class Workbench providers rather than
unrelated executables:

| Application | Core features |
|---|---|
| Drive/Documents | Files, folders, metadata, tags, sharing, versions, retention |
| Calendar | Calendars, recurrence, availability, invitations, enterprise resources |
| Contacts | Personal contacts plus governed enterprise customer/contact views |
| Mail | Accounts, folders, search, threads, calendar/contact integration |
| Forms | Form designer, validation, submissions, approval and enterprise write commands |
| PDF | View, annotate, redact, combine, sign, export |
| Notes/Knowledge | Pages, backlinks, hierarchy, search, permissions, attachments |
| Draw/Diagram | Vector drawing, flowcharts, architecture and organization diagrams |
| Database/Base | Query, form, view, report designer over governed data sources |
| Publisher | Brochure, label, newsletter, print layout |
| Dashboard/BI | Metrics, charts, semantic dimensions, filters, scheduled reports |
| Sign | Signature requests, signer identity, immutable audit record |

---

## 3. Enterprise feature gaps

### 3.1 Common enterprise foundation

This layer should be completed before expanding every domain independently.

P0

- Identity, MFA, SSO, service accounts, session lifecycle.
- Tenant, legal entity, business unit, location, team, and cost-center model.
- RBAC plus object-, row-, field-, and action-level policy evaluation.
- Separation of duties.
- Common master-data IDs and reference-data service.
- Workflow and approval engine.
- Attachments, comments, tasks, notifications, and audit events.
- Idempotency, optimistic concurrency, outbox, and durable transaction evidence.
- API versioning, webhooks, connector jobs, import/export.
- Localization framework for currency, calendars, tax, address, and numbering.
- Data classification, privacy, retention, and deletion policy.
- Backup, restore, migration, upgrade, and rollback procedures.

P1

- Delegation and temporary authority.
- Organization-wide search.
- Rules and automation builder.
- Scheduled jobs and reports.
- Configurable custom fields and views.
- Sandbox/test tenant.
- Operational administration console.
- Data quality and duplicate management.

### 3.2 CRM and sales

The existing lead/opportunity state machine should remain the core, surrounded
by these bounded capabilities:

**Customer and contact**

- Accounts, contacts, households or organizations.
- Parent-child account hierarchy.
- Addresses, communication channels, consent, preferences.
- Customer 360 timeline.
- Duplicate detection and controlled merge.
- Customer classification, territory, owner, and account team.

**Lead management**

- Capture from forms, import, email, API, and campaigns.
- Assignment and routing.
- Qualification policy.
- Scoring and enrichment.
- Duplicate prevention.
- Conversion to account/contact/opportunity.

**Opportunity management**

- Configurable stages and required fields.
- Products, quantities, expected revenue, probability.
- Competitors and loss reasons.
- Activities, tasks, meetings, and reminders.
- Team selling and territory assignment.
- Forecast categories and weighted pipeline.
- Stage history and duration analysis.

**Quote-to-cash**

- Price books and discount policy.
- Quotations and revisions.
- Approval thresholds.
- Contract and signature.
- Sales order.
- Fulfillment and delivery.
- Invoice and payment status.
- Returns, refunds, and credit notes.
- Subscription and renewal support.

**Marketing and service**

- Campaigns and attribution.
- Segmentation and consent.
- Cases, queues, SLA, escalation.
- Knowledge articles.
- Field service and customer portal.

### 3.3 Finance

Current finance kernels should evolve into an operational accounting system:

- Chart of accounts and accounting dimensions.
- Journals and immutable postings.
- Accounts receivable and payable.
- Customer and supplier invoices.
- Payments, allocations, refunds, write-offs.
- Bank import and reconciliation.
- Tax calculation, reporting, and localization packs.
- Fixed assets and depreciation.
- Budgeting and forecasting.
- Accruals, allocations, recurring journals.
- Multi-currency and realized/unrealized FX.
- Period close, lock, reopen, and approval.
- Consolidation and intercompany elimination.
- Cash flow and financial statements.
- Audit export.

### 3.4 Inventory, procurement, and logistics

**Inventory/WMS**

- Warehouses, zones, bins, and locations.
- Stock ledger and valuation.
- Lot, serial, expiration, and traceability.
- Reservation and available-to-promise.
- Receipt, put-away, transfer, pick, pack, ship.
- Cycle counts and adjustments.
- Barcode operations.
- Replenishment, reorder policy, and safety stock.
- Landed cost.
- Returns and RMA.

**Procurement**

- Supplier onboarding and qualification.
- Requisition and approval.
- RFQ/tender and comparison.
- Contract and price agreement.
- Purchase order and change order.
- Receipt and inspection.
- Three-way matching.
- Supplier invoice.
- Supplier performance and spend analytics.

### 3.5 Manufacturing, HCM, projects, and service

**Manufacturing**

- BOM and revisions.
- Routings and work centers.
- MRP and capacity planning.
- Work orders and job cards.
- Material issue, consumption, and production receipt.
- WIP and variance costing.
- Quality plans, inspections, nonconformance.
- Maintenance and downtime.
- Engineering change control.

**HCM**

- Organization and positions.
- Recruiting and candidate tracking.
- Onboarding and offboarding.
- Employee contracts and documents.
- Attendance, schedules, time, and leave.
- Expenses and approvals.
- Performance and goals.
- Learning and certification.
- Benefits and payroll country packs.
- Employee and manager self-service.

**Projects and service**

- Projects, milestones, tasks, dependencies.
- Resource and capacity planning.
- Timesheets and expenses.
- Billing and revenue recognition.
- Helpdesk queues, tickets, SLA, escalation.
- Field-service dispatch.
- Knowledge base and customer portal.

---

## 4. Target architecture

### 4.1 Product topology

```
┌──────────────────────────────────────────────────────────────┐
│                    Simple Workbench                           │
│                                                              │
│ Activity bar │ Sidebars │ Editor groups │ Panel │ Status bar │
│ Command palette │ Search │ Test explorer │ Notifications      │
├──────────────────────────────────────────────────────────────┤
│ Editor/View Providers                                        │
│                                                              │
│ Code │ Writer │ Calc │ Slides │ PDF │ DB │ Dashboard │ CRM   │
│ Finance │ Inventory │ HCM │ Admin │ Test/Debug                │
├──────────────────────────────────────────────────────────────┤
│ Browser Extension Host / Desktop Plugin Host / TUI Adapter    │
├─────────────────────┬──────────────────────┬─────────────────┤
│ Document SDK        │ Enterprise SDK       │ Platform SDK    │
│                     │                      │                 │
│ Session             │ Query                │ Commands        │
│ Version             │ Snapshot             │ Filesystem      │
│ Lock                │ Binding              │ Auth            │
│ Conversion          │ Command/write-back   │ Notifications   │
│ Collaboration       │ Audit/provenance     │ Diagnostics     │
├─────────────────────┴──────────────────────┴─────────────────┤
│ Backend services                                             │
│                                                              │
│ Document service │ Enterprise modular monolith │ Identity     │
│ Conversion worker │ Collaboration service │ Search/indexing  │
│ Connector jobs │ Notification worker │ Observability         │
├──────────────────────────────────────────────────────────────┤
│ PostgreSQL │ Object storage │ Cache/lock store │ Search index │
└──────────────────────────────────────────────────────────────┘
```

### 4.2 Deployment strategy

Use a modular monolith for the enterprise transaction system initially. Domain
boundaries should be explicit, but transactions involving sales, inventory,
invoicing, and accounting should not be distributed across premature
microservices.

Separate only components with materially different runtime properties:

- Document conversion worker.
- Browser editing/document-session server.
- Collaboration/presence server.
- Search indexing.
- Connector and scheduled-job workers.
- Large report or spreadsheet computation workers.

Recommended persistence roles:

```
PostgreSQL:
    authoritative enterprise transactions and metadata

Object storage:
    documents, attachments, exports, thumbnails

SQLite:
    local development, bounded offline work, test fixtures
    not the authoritative multi-user enterprise ledger

Cache/lock service:
    presence, short-lived sessions, distributed locks, job coordination

Search index:
    document and enterprise full-text search
```

### 4.3 Hybrid Office editor strategy

Building full Word, Excel, and PowerPoint compatibility, pagination,
rendering, collaboration, and format fidelity natively is a very large
undertaking. A two-track strategy is safer.

**Track A — native Simple editors**

Use the existing Simple models for:

- Markdown.
- Simple native document formats.
- ODF-oriented documents where supported.
- Lightweight Writer and Calc use.
- Embedded and Simple OS deployments.
- Specialized enterprise forms and reports.

**Track B — document-server adapter**

For high-fidelity DOCX/XLSX/PPTX browser editing, initially support a
WOPI-like document-session adapter to a mature document server. A conforming
edit flow needs file information, file retrieval, save, save-as, lock, unlock,
lock refresh, and relock behavior. ONLYOFFICE's documented architecture
illustrates the separation: the integrating application owns authentication,
storage, and document management, while the document server provides editing,
conversion, command, and builder services. Its WOPI support exposes discovery,
file, lock, refresh, unlock, and save operations.

This should be an adapter, not a hard-coded dependency:

```
DocumentEditorProvider
    ├── SimpleNativeEditorProvider
    ├── WopiEditorProvider
    └── FutureExternalEditorProvider
```

A license and deployment review is required for every external provider.
Protocol compatibility alone does not confer rights to embed a commercial
online editor.

---

## 5. Enterprise data inside Calc, Writer, and Slides

### 5.1 Do not give documents direct database access

Office files must never contain database credentials or execute arbitrary SQL
against enterprise tables.

Use this flow:

```
Office document
    ↓ binding ID
Enterprise Binding Service
    ↓ named, versioned query
Authorization and policy engine
    ↓ tenant/row/field filtering
Enterprise read model
    ↓ immutable snapshot
Office renderer
```

All write operations must pass through validated enterprise commands:

```
Document edit
    ↓ explicit "Submit changes"
Domain command
    ↓ authorization + validation + approval
Transaction
    ↓ outbox + audit event
Updated read model
```

Formulas should be read-only. A formula recalculation must never mutate
inventory, create an invoice, or update a customer.

### 5.2 Core binding contracts

Illustrative contract design:

```
EnterpriseDataSource {
    id
    tenant_id
    name
    query_id
    query_version
    parameters_schema
    result_schema
    policy_id
    refresh_policy
    classification
}

EnterpriseQueryRequest {
    source_id
    parameters
    requested_fields
    filter
    sort
    page
    document_context
}

DataSnapshot {
    source_id
    query_version
    snapshot_version
    schema
    rows
    created_at
    as_of
    content_hash
    policy_decision_id
    provenance
}

DocumentBinding {
    id
    document_id
    document_version
    source_id
    target_kind
    target_reference
    field_mapping
    presentation_options
    refresh_mode
    writeback_policy
}

EnterpriseWriteCommand {
    command_type
    aggregate_id
    expected_version
    idempotency_key
    payload
    approval_context
    source_document_id
    source_document_version
}
```

Binding target kinds:

```
calc_table
calc_cell
calc_named_range
calc_pivot
calc_chart
writer_content_control
writer_repeat_section
writer_conditional_section
slides_chart
slides_table
slides_kpi
mail_merge_field
publisher_field
```

### 5.3 Calc integration

Example user flow:

```
Insert
  → Enterprise Data
  → CRM
  → Opportunities
```

The query builder lets the user choose:

- Tenant and business unit.
- Sales team and owner.
- Stage.
- Expected close date range.
- Currency.
- Requested dimensions and measures.
- Snapshot or live-refresh behavior.

The result is inserted as a managed table:

```
Opportunity
Account
Owner
Stage
ExpectedAmount
Probability
WeightedAmount
ExpectedCloseDate
LastActivityAt
```

The workbook stores only:

- Binding ID.
- Query version.
- Parameter values.
- Presentation mapping.
- Last snapshot hash.
- Last refresh timestamp.

It does not store a reusable database credential.

Recommended read-only functions:

```
=ENT.VALUE("crm.pipeline", "open_amount")
=ENT.VALUE("inventory.summary", "available_quantity", A2)
=ENT.SNAPSHOT_TIME("crm-opportunities")
=ENT.IS_STALE("crm-opportunities")
```

Large tabular results should be managed data tables rather than formula
arrays.

**Write-back**

Editing a managed row should not immediately update CRM. The user explicitly
enters a review surface:

```
Review changes
    → validate
    → show conflicts
    → request approval when required
    → submit domain commands
```

Every changed row includes:

```
record ID
original version
changed fields
validation result
authorization result
command idempotency key
```

### 5.4 Writer integration

Writer should support enterprise-bound content controls similar to the broadly
used document-content-control pattern, where structured document elements are
bound to managed data. Microsoft Word's add-in and content-control APIs
demonstrate bidirectional structured bindings, repeated content, tables, and
task-pane integration.

Example quotation template:

```
Customer name:       {{crm.account.name}}
Billing address:     {{crm.account.billing_address}}
Opportunity:         {{crm.opportunity.name}}
Quote number:        {{sales.quote.number}}
Valid until:         {{sales.quote.valid_until}}

{{#repeat sales.quote.lines}}
  {{product.name}}
  {{quantity}}
  {{unit_price}}
  {{discount}}
  {{line_total}}
{{/repeat}}

Subtotal:            {{sales.quote.subtotal}}
Tax:                 {{sales.quote.tax}}
Total:               {{sales.quote.total}}
```

Required behavior:

- Bound fields can be locked or editable according to policy.
- Repeated sections render quote lines.
- Narrative sections remain ordinary Writer content.
- A generated quotation records the exact enterprise snapshot hash.
- Refresh shows a diff before replacing changed bound values.
- Finalized quotations freeze their snapshot.
- Regeneration creates a new document version.
- Export includes classification and provenance metadata.
- Unauthorized fields remain masked even when a previous user created the
  document.

### 5.5 Slides and dashboards

Slides should support linked:

- KPI cards.
- Tables.
- Charts.
- Pipeline funnels.
- Financial statements.
- Inventory summaries.
- Project status data.

Two modes are needed:

```
Live presentation:
    refreshes authorized data on request

Published presentation:
    preserves an immutable, timestamped snapshot
```

A data-change event should normally mark a slide or workbook as stale rather
than silently rewriting an open document:

```
crm.opportunity.changed
    → binding marked stale
    → user receives refresh indicator
    → user previews differences
    → refresh creates document version
```

---

## 6. Simple Workbench and web launch

### 6.1 Turn the IDE into the real workbench

The immediate refactor should introduce one composition entry point:

```
workbench_launch(config)
```

Both the existing IDE and editor executables call it:

```
simple ide
simple office
simple writer
simple calc
simple enterprise
```

These become launch profiles, not separate UI architectures.

Example:

```
simple workbench --desktop
simple workbench --web --listen 127.0.0.1:8080
simple workbench --tui
simple workbench --open document://quote/123
simple workbench --open enterprise://crm/opportunity/456
```

### 6.2 Workbench layout

The shared shell should provide:

- Activity bar.
- Primary and secondary sidebars.
- Split editor groups.
- Bottom panel.
- Status bar.
- Command palette.
- Search.
- Outline and navigation.
- Problems and diagnostics.
- Test explorer.
- Source control.
- Notifications.
- Account and tenant switcher.
- Restoreable layouts.
- Keyboard mapping and accessibility model.

VS Code's browser and desktop architecture provides a useful reference:
extensions may run locally, in a browser worker, or in a remote extension
host, while the workbench provides persistent editor groups, sidebars, panels,
commands, and view contributions. Web extensions run in a browser sandbox
without unrestricted Node access.

### 6.3 Provider model

```
EditorProvider
ViewProvider
CommandProvider
MenuProvider
FileSystemProvider
SearchProvider
DocumentProvider
EnterpriseDataSourceProvider
ReportProvider
Exporter
Importer
AuthenticationProvider
TestProvider
DiagnosticProvider
```

Every provider declares:

```
id
version
runtime: browser | desktop | server | tui
permissions
commands
document types
views
dependencies
activation events
```

Do not allow extensions to directly mutate the workbench DOM. They contribute
through stable APIs and isolated webviews or component trees. Workspace Trust
or an equivalent policy should restrict extensions and workspaces capable of
executing code.

### 6.4 Browser runtime

Recommended browser decomposition:

```
Browser main thread:
    Workbench UI and editor rendering

Web Worker:
    plugin host
    formula engine where appropriate
    parser and non-UI transforms

Backend:
    workspace and filesystem
    document session
    enterprise queries
    authentication
    conversion
    search
```

The browser version should run in Chromium, Firefox, and WebKit first. The
Simple browser should be an additional differential and deployment target, not
a prerequisite for launching the first web Office release. Otherwise every
Office defect will be confounded with an unfinished browser-engine defect.

Recommended deep links:

```
/workbench
/office/document/{document_id}
/office/workbook/{document_id}
/office/presentation/{document_id}
/enterprise/crm/opportunities/{id}
/enterprise/sales/quotes/{id}
/enterprise/finance/invoices/{id}
```

### 6.5 Proposed source organization

```
src/app/workbench/
    main.spl
    desktop_main.spl
    web_main.spl
    tui_main.spl

src/lib/workbench/
    model/
    layout/
    commands/
    menus/
    views/
    editor/
    plugin_host/
    permissions/
    navigation/

src/lib/document/
    document_id.spl
    metadata.spl
    content_store.spl
    session.spl
    version.spl
    lock.spl
    autosave.spl
    conversion.spl
    collaboration.spl
    audit.spl

src/lib/enterprise_binding/
    data_source.spl
    query.spl
    schema.spl
    snapshot.spl
    binding.spl
    refresh.spl
    provenance.spl
    writeback.spl

src/app/office/web/
    routes.spl
    bootstrap.spl
    editor_host.spl
    document_adapter.spl

src/app/enterprise_workbench/
    crm/
    sales/
    finance/
    inventory/
    procurement/
    manufacturing/
    hcm/
    projects/
    service/
```

Preserve existing Office and editor code behind adapters during migration. Do
not attempt a destructive rewrite.

---

## 7. Intensive test architecture

### 7.1 Gate T0 — evidence integrity

This gate precedes all product completion claims.

Every test receipt must include:

```
repository revision
binary SHA-256
compiler/runtime identity
self-hosted or seed provenance
host OS and architecture
test suite
selected count
executed count
passed count
failed count
skipped count
wall-clock duration
artifact paths
exit status
```

Anti-vacuity checks:

- Executed count must be greater than zero.
- A production receipt cannot use the seed interpreter unless explicitly allowed.
- A zero-duration suite is rejected unless a high-resolution timer proves it
  legitimate.
- Every expected fixture must be enumerated before running.
- Temporarily removing one fixture must fail the enumeration gate.
- Temporarily breaking one assertion must fail the suite.
- "Unsupported" cannot silently become "passed."
- Capability metadata cannot advance without the required receipt level.

### 7.2 Test suites

| Suite | Required tests |
|---|---|
| Runtime/native | Self-hosted compiler launch, native DB operations, true transaction rollback, constraint failures, crash behavior |
| Workbench | Launch, restore layout, command palette, tabs, splits, views, extension activation, keyboard navigation |
| Document session | Create/open/save/save-as, version conflicts, lock lifecycle, stale token, recovery |
| Writer | Editing, styles, pagination, tables, images, sections, headers/footers, comments, track changes |
| Calc | Formula compatibility, dependency graphs, spills, circular references, locale/date behavior, large workbooks |
| Slides | Masters, layouts, charts, media, notes, presentation mode, export |
| Formats | DOCX/ODT/XLSX/ODS/PPTX import-export, structural preservation, visual comparison |
| Enterprise binding | Query schema, authorization, refresh, stale data, snapshot, provenance, export, write-back |
| Business E2E | Lead-to-cash, procure-to-pay, record-to-report, hire-to-retire, manufacture-to-stock |
| Collaboration | Concurrent edits, offline edits, reconnect, duplicate/reordered operations, compaction |
| Security | Tenant isolation, BOLA, field leakage, CSRF, XSS, SSRF, upload attacks, formula injection |
| Durability | Kill at transaction boundaries, disk full, network failure, backup, restore, migration rollback |
| Accessibility | Keyboard-only, no traps, focus order, screen-reader grids, zoom, high contrast, IME and RTL |
| Performance | Startup, first interaction, save, refresh, recalculation, scroll, concurrent sessions |
| Cross-platform | Windows, Linux, macOS, browser engines, Simple OS when native gate passes |
| Release | Upgrade N−1 to N, rollback, deterministic build, SBOM, signature, compatibility |

### 7.3 Format compatibility corpus

Target current standardized formats rather than only self-generated samples.
OOXML's packaging and vocabulary requirements are specified by ECMA-376, while
ODF 1.4 became an approved OASIS standard in December 2025.

The corpus should include, per major format:

- Minimal documents.
- Realistic business documents.
- Large documents.
- Documents generated by Microsoft Office.
- Documents generated by LibreOffice.
- Documents generated by Google export.
- Unknown but valid extension content.
- Malformed ZIP packages.
- Missing relationships.
- Duplicate relationships.
- XML entity and external-resource attacks.
- ZIP bombs and oversized entries.
- Unsupported macros.
- Embedded objects.
- Fonts unavailable on the test system.
- Mixed locale and calendar values.

Validation layers:

```
1. Package validity
2. XML/schema validity
3. Semantic document model
4. Import → export preservation
5. Reopen exported file
6. Visual raster comparison
7. Accessibility metadata preservation
8. Performance and memory limits
```

Unsupported elements should be preserved where possible, even if Simple cannot
render or edit them.

### 7.4 Calc property and differential tests

Required randomized invariants:

- Recalculation order does not change results.
- Unrelated cell edits do not recalculate unaffected subgraphs.
- Copy/paste preserves relative and absolute references.
- Insert/delete row adjusts references correctly.
- Undo restores the prior dependency graph.
- Save/reopen preserves values, formulas, styles, and named ranges.
- Parallel recalculation equals deterministic single-thread recalculation.
- Locale changes affect presentation, not stored numeric meaning.
- Formula errors propagate according to specification.
- A cycle is rejected or iterated according to explicit workbook policy.

Differential testing:

```
same workbook
    → Simple Calc
    → LibreOffice Calc
    → Microsoft Excel where test infrastructure permits
    → compare values, errors, formats, and exported structure
```

### 7.5 Enterprise binding security tests

Every data source needs tests for:

- Cross-tenant object access.
- Cross-tenant record identifiers.
- Field-level masking.
- Revoked access after a document was created.
- Export after access revocation.
- Hidden columns and cached values.
- Query-parameter tampering.
- Pagination and sorting authorization.
- Snapshot replay.
- Stale snapshot refresh.
- Malicious text beginning with `=`, `+`, `-`, or `@`.
- Formula injection in CSV export.
- HTML/script injection into Writer or Slides.
- Oversized enterprise result sets.
- Unauthorized write-back.
- Duplicate write-back submission.
- Optimistic-concurrency conflict.
- Approval bypass.
- Transaction rollback.
- Audit event immutability.

Security acceptance should be mapped to OWASP ASVS 5.0 and the OWASP API
Security Top 10, including object-level authorization, authentication,
property-level authorization, function-level authorization, resource
consumption, SSRF, and unsafe third-party API consumption.

### 7.6 Accessibility and observability

The workbench and Office editors should target WCAG 2.2 AA behavior, including
keyboard access, no keyboard traps, visible and unobscured focus, adequate
target sizes, and accessible authentication. WCAG2ICT should be applied to
non-web desktop and embedded surfaces.

Every browser-to-database flow should carry one correlation context:

```
browser action
  → workbench command
  → document session
  → enterprise query
  → policy decision
  → database call
  → snapshot
  → rendering
```

Use OpenTelemetry-compatible traces, metrics, and logs so document IDs, query
IDs, policy-decision IDs, audit IDs, and failures can be correlated without
logging sensitive field values.

---

## 8. Parallel development plan

### 8.1 Contract freeze before parallel implementation

Freeze these interfaces first:

```
WorkbenchContribution
DocumentId
DocumentMetadata
DocumentSession
DocumentVersion
DocumentLock
EnterpriseDataSource
EnterpriseQuery
DataSnapshot
DocumentBinding
EnterpriseCommand
PolicyDecision
AuditEvent
```

Agents can then implement behind the interfaces without repeatedly modifying
shared files.

Designate one integration owner for:

- `src/app/office/mod.spl`
- `src/app/enterprise_store_app/main.spl`
- global command registry
- global route registry
- shared migrations
- plugin catalog

Other agents submit declarative registration fragments; they do not directly
edit those hot files.

### 8.2 Parallel lanes

| Lane | Ownership | Main result | Dependencies |
|---|---|---|---|
| A. Evidence/runtime | Compiler, runtime, test receipts | Self-hosted executable and trustworthy native evidence | None |
| B. Workbench shell | src/app/ide, editor core, workbench | Real desktop/web/TUI application shell | Frozen workbench contracts |
| C. Document service | Document metadata, content, versions, locks | Durable open/save/autosave/version API | Storage contract |
| D. Web document adapter | Web host, WOPI-like adapter | High-fidelity browser editor integration | C |
| E. Enterprise query SDK | Named queries, schemas, snapshots | Governed read API | Policy and tenant contracts |
| F. Security/governance | Identity, RBAC/ABAC, audit, classification | Shared policy enforcement | Foundation contracts |
| G. CRM and sales | CRM, accounts, contacts, quotes | Lead-to-opportunity-to-quote domain | E and F |
| H. Calc bindings | Managed tables, refresh, provenance | CRM pipeline in Calc | E |
| I. Writer/Slides bindings | Content controls, templates, linked charts | Generated quotation and reports | C and E |
| J. Collaboration | Presence, conflict handling, operation log | Concurrent native editing | C |
| K. Format/fidelity | OOXML/ODF, renderer, conversion | Repeatable compatibility corpus | C |
| L. QA/security/performance | System tests, fuzzing, benchmarks | Release gates and receipts | All lanes incrementally |
| M. Enterprise verticals | Finance, inventory, procurement, HCM | Expanded business flows | E and F |
| N. Operations | Deployment, backup, restore, telemetry | Reproducible production environment | A, C, E, F |

Lanes A, B, C, E, F, K, and L can begin concurrently after the first contract
freeze. The golden integrated flow begins when B, C, E, F, G, H, and I have
their first contract-conforming slices.

### 8.3 Delivery waves

**Gate 0 — establish truth**

Required before claiming a production-capable feature:

- Self-hosted binary identity is proven.
- Native tests execute with non-vacuous receipts.
- Real SQLite or PostgreSQL transaction behavior is proven.
- Rollback, constraints, idempotency, and outbox behavior are tested.
- `simple ide` enters a real shell rather than printing readiness.
- Browser system tests launch a real workbench.

**Wave 1 — common foundation**

Deliver:

- Simple Workbench desktop and browser shell.
- Document ID, metadata, object storage, version, and session contracts.
- Enterprise data source, query, snapshot, and binding contracts.
- Identity, tenant, authorization, and audit foundation.
- Capability-status evidence manifest.
- Initial format corpus and release receipts.

**Wave 2 — golden vertical slice**

Deliver this exact scenario:

1. Salesperson signs in.
2. Creates a lead.
3. Qualifies it.
4. Opens an opportunity.
5. Adds customer and product information.
6. Opens Calc in the Workbench.
7. Inserts an authorized opportunity pipeline table.
8. Refreshes it and creates a chart.
9. Opens a Writer quotation template.
10. Binds customer, opportunity, and line-item fields.
11. Saves a version.
12. Exports DOCX and PDF.
13. Unauthorized user is unable to refresh or export protected fields.
14. One trace connects user action, document version, query snapshot, policy
    decision, and audit event.

**Wave 3 — practical SMB suite**

- Accounts and contacts.
- Activities, meetings, email links, reminders.
- Quote approvals, order, inventory reservation, invoice, payment.
- Procurement and supplier flow.
- Basic GL, AR, AP, and bank reconciliation.
- HCM employee, time, leave, and expenses.
- Document comments, sharing, review, and notification.
- Scheduled data refresh and reports.
- CRM, sales, finance, and inventory Workbench views.

**Wave 4 — collaboration and depth**

- Concurrent editing and presence.
- Offline/reconnect behavior.
- Track changes and comments.
- Advanced Writer layout.
- Advanced Calc analysis.
- Slide masters and presenter mode.
- Manufacturing, projects, service, payroll, and localization.
- Search, DLP, retention, e-signature, and administration.

**Wave 5 — production hardening**

- Cross-browser and cross-platform certification.
- Large-document and high-concurrency benchmarks.
- Disaster recovery and point-in-time restore.
- Upgrade and rollback testing.
- Security review against ASVS.
- Accessibility audit.
- Signed deterministic builds and SBOM.
- Production SLOs, alerts, and operational runbooks.

---

## 9. Recommended first merge sequence

1. Replace `implemented: true` with the evidence-based capability-status model.
2. Rename user-visible LibreOffice identifiers to Simple Office.
3. Introduce `workbench_launch()` and make `src/app/ide/main.spl` enter the
   actual shell.
4. Move editor, Office, and enterprise contributions behind provider
   interfaces.
5. Add document metadata, version, session, lock, and autosave contracts.
6. Establish trustworthy native DB and self-hosted test receipts.
7. Add the versioned Enterprise Data Source and Snapshot contracts.
8. Extend CRM with accounts, contacts, activities, and opportunity products.
9. Add CRM and sales Workbench views and API routes.
10. Implement Calc managed enterprise tables.
11. Implement Writer content controls and repeated enterprise sections.
12. Complete the CRM → Calc → Writer quotation golden-flow system test.
13. Add the external browser document-provider adapter.
14. Add collaboration, comments, and review.
15. Expand the same integration pattern to finance, inventory, procurement,
    and HCM.

---

## 10. Definition of done for the first integrated release

The first release is complete only when all of the following are true:

- `simple ide` launches a persistent Workbench.
- The same workspace opens in browser and desktop modes.
- A document has a stable ID, versions, autosave, and recovery.
- A user can create and advance a CRM opportunity.
- CRM data can be inserted into Calc through a governed named data source.
- Refresh re-evaluates tenant, row, and field authorization.
- A Writer quotation can bind customer and line-item data.
- The final document records its enterprise snapshot and provenance.
- A conflicting update is detected rather than overwritten.
- Write-back uses explicit commands with idempotency and expected versions.
- DOCX, XLSX, and PDF artifacts reopen successfully.
- Browser E2E passes on Chromium, Firefox, and WebKit.
- Native transaction, rollback, and crash-recovery tests pass.
- Security tests prove cross-tenant access is impossible.
- Accessibility tests prove complete keyboard operation.
- A single trace links the UI action to document, enterprise query,
  transaction, and audit event.
- Every completion claim references a reproducible test receipt.

The correct immediate objective is therefore not "finish all Office and ERP
modules." It is to create the common Workbench, document-session layer, and
enterprise-binding contract, then prove them through the CRM-to-quotation
vertical slice. Once that path is reliable, the existing Office and enterprise
kernels can be expanded in parallel without creating another set of isolated
applications.
