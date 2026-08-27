# Enterprise Channel Hub — SPI, mock channel, import, reconcile

> Specs for `std.enterprise_channel` (sync-tier impl `src/lib/nogc_sync_mut/enterprise_channel/channel_hub.spl`): the generic channel adapter SPI (mode-struct, like the outbox worker's DispatchTarget), the deterministic mock channel, the guarded checkpointed import flow into `sale_place_order`, the kill switch, acknowledgements, and reconciliation as data.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Channel Hub — SPI, mock channel, import, reconcile

Specs for `std.enterprise_channel` (sync-tier impl `src/lib/nogc_sync_mut/enterprise_channel/channel_hub.spl`): the generic channel adapter SPI (mode-struct, like the outbox worker's DispatchTarget), the deterministic mock channel, the guarded checkpointed import flow into `sale_place_order`, the kill switch, acknowledgements, and reconciliation as data.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §8 |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Specs for `std.enterprise_channel` (sync-tier impl
`src/lib/nogc_sync_mut/enterprise_channel/channel_hub.spl`): the generic
channel adapter SPI (mode-struct, like the outbox worker's DispatchTarget),
the deterministic mock channel, the guarded checkpointed import flow into
`sale_place_order`, the kill switch, acknowledgements, and reconciliation
as data.

Contract under test: fetch is at-least-once (cursor holds at the last
successful page on provider failure); the internal EFFECT is exactly-once —
inbox dedup by external order id plus sale-level idempotency
(`chan:<channel>:<external_id>`). Rollout step 1 only: mock channel; Amazon
is future work behind the same SPI.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §8
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W5-C, channel hub §8, rollout step 1).

## Scenarios

### channel hub — mock adapter SPI

#### pages scripted orders deterministically by cursor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pages scripted orders deterministically by cursor
- Page 1 from the empty cursor
   - Expected: p1.orders.len() equals `2`
   - Expected: p1.orders[0].external_id equals `ext-100`
   - Expected: p1.next_cursor equals `2`
- Page 2 resumes exactly where page 1 ended
   - Expected: p2.orders.len() equals `2`
   - Expected: p2.orders[0].external_id equals `ext-102`
- Past the end the page is empty (script exhausted)
   - Expected: p3.orders.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pages scripted orders deterministically by cursor")
val adapter = mock_channel(scripted_orders(), 2)
step("Page 1 from the empty cursor")
val p1 = channel_fetch_orders(adapter, "")
expect(p1.ok).to_be(true)
expect(p1.orders.len()).to_equal(2)
expect(p1.orders[0].external_id).to_equal("ext-100")
expect(p1.next_cursor).to_equal("2")
step("Page 2 resumes exactly where page 1 ended")
val p2 = channel_fetch_orders(adapter, p1.next_cursor)
expect(p2.orders.len()).to_equal(2)
expect(p2.orders[0].external_id).to_equal("ext-102")
step("Past the end the page is empty (script exhausted)")
val p3 = channel_fetch_orders(adapter, p2.next_cursor)
expect(p3.ok).to_be(true)
expect(p3.orders.len()).to_equal(0)
```

</details>

### channel hub — import happy path over two pages

#### imports every external order as exactly one internal order via the cursor

- imports every external order as exactly one internal order via the cursor
- Import a full batch — two pages via cursor
   - Expected: rep.fetched equals `4`
   - Expected: rep.imported equals `4`
   - Expected: rep.duplicates equals `0`
   - Expected: rep.cursor equals `4`
- Each external order produced a created internal order; stock reserved; journal balanced
   - Expected: sale_order_status(store, "tenant-a", "chan-mock-1-ext-100") equals `created`
   - Expected: sale_order_status(store, "tenant-a", "chan-mock-1-ext-103") equals `created`
   - Expected: sale_available_stock(store, "tenant-a", "widget-1") equals `90`
   - Expected: channel_inbox_count(store, "tenant-a", "mock-1") equals `4`
   - Expected: channel_cursor(store, "tenant-a", "mock-1") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("imports every external order as exactly one internal order via the cursor")
val store = fresh_store()
val t = tenant_a()
val a = admin()
val s = session_for(t, a)
val adapter = mock_channel(scripted_orders(), 2)
step("Import a full batch — two pages via cursor")
val rep = channel_import_orders(store, s, t, a, env("imp-1"), adapter, "mock-1", 10)
expect(rep.ok).to_be(true)
expect(rep.fetched).to_equal(4)
expect(rep.imported).to_equal(4)
expect(rep.duplicates).to_equal(0)
expect(rep.cursor).to_equal("4")
step("Each external order produced a created internal order; stock reserved; journal balanced")
expect(sale_order_status(store, "tenant-a", "chan-mock-1-ext-100")).to_equal("created")
expect(sale_order_status(store, "tenant-a", "chan-mock-1-ext-103")).to_equal("created")
expect(sale_available_stock(store, "tenant-a", "widget-1")).to_equal(90)
expect(sale_journal_balanced(store, "tenant-a")).to_be(true)
expect(channel_inbox_count(store, "tenant-a", "mock-1")).to_equal(4)
expect(channel_cursor(store, "tenant-a", "mock-1")).to_equal("4")
store_close(store)
```

</details>

### channel hub — replayed import is exactly-once

#### re-running the import produces zero new internal effects

- re-running the import produces zero new internal effects
- Replay the import from a reset cursor position (fresh adapter, same script)
- All 4 are recorded results — dedup by external order id, no second effect
   - Expected: rep2.fetched equals `4`
   - Expected: rep2.imported equals `0`
   - Expected: rep2.duplicates equals `4`
   - Expected: channel_inbox_count(store, "tenant-a", "mock-1") equals `4`
   - Expected: sale_available_stock(store, "tenant-a", "widget-1") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-running the import produces zero new internal effects")
val store = fresh_store()
val t = tenant_a()
val a = admin()
val s = session_for(t, a)
val adapter = mock_channel(scripted_orders(), 2)
channel_import_orders(store, s, t, a, env("imp-1"), adapter, "mock-1", 10)
step("Replay the import from a reset cursor position (fresh adapter, same script)")
store_insert_row(store,
    "INSERT INTO channel_checkpoints (tenant_id, channel_id, cursor) VALUES (?, ?, ?)",
    ["tenant-a", "mock-1", ""])
val rep2 = channel_import_orders(store, s, t, a, env("imp-2"), adapter, "mock-1", 10)
step("All 4 are recorded results — dedup by external order id, no second effect")
expect(rep2.fetched).to_equal(4)
expect(rep2.imported).to_equal(0)
expect(rep2.duplicates).to_equal(4)
expect(channel_inbox_count(store, "tenant-a", "mock-1")).to_equal(4)
expect(sale_available_stock(store, "tenant-a", "widget-1")).to_equal(90)
store_close(store)
```

</details>

### channel hub — provider failure mid-batch holds the cursor

#### keeps the checkpoint at the last success and completes on rerun without duplicates

- keeps the checkpoint at the last success and completes on rerun without duplicates
- Import with a provider that fails at cursor 2 (page 2)
   - Expected: rep1.reason equals `store-error`
   - Expected: rep1.imported equals `2`
- Cursor holds at the last successful page
   - Expected: channel_cursor(store, "tenant-a", "mock-1") equals `2`
- Rerun with a healthy provider — resumes at 2, completes, zero duplicates
   - Expected: rep2.fetched equals `2`
   - Expected: rep2.imported equals `2`
   - Expected: rep2.duplicates equals `0`
   - Expected: channel_inbox_count(store, "tenant-a", "mock-1") equals `4`
   - Expected: sale_available_stock(store, "tenant-a", "widget-1") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the checkpoint at the last success and completes on rerun without duplicates")
val store = fresh_store()
val t = tenant_a()
val a = admin()
val s = session_for(t, a)
step("Import with a provider that fails at cursor 2 (page 2)")
val bad = mock_channel_failing(scripted_orders(), 2, "2")
val rep1 = channel_import_orders(store, s, t, a, env("imp-1"), bad, "mock-1", 10)
expect(rep1.ok).to_be(false)
expect(rep1.reason).to_equal("store-error")
expect(rep1.imported).to_equal(2)
step("Cursor holds at the last successful page")
expect(channel_cursor(store, "tenant-a", "mock-1")).to_equal("2")
step("Rerun with a healthy provider — resumes at 2, completes, zero duplicates")
val good = mock_channel(scripted_orders(), 2)
val rep2 = channel_import_orders(store, s, t, a, env("imp-2"), good, "mock-1", 10)
expect(rep2.ok).to_be(true)
expect(rep2.fetched).to_equal(2)
expect(rep2.imported).to_equal(2)
expect(rep2.duplicates).to_equal(0)
expect(channel_inbox_count(store, "tenant-a", "mock-1")).to_equal(4)
expect(sale_available_stock(store, "tenant-a", "widget-1")).to_equal(90)
store_close(store)
```

</details>

### channel hub — kill switch

#### denies every hub operation on a killed channel with reason forbidden

- denies every hub operation on a killed channel with reason forbidden
- Kill the channel
- Import, listing publish, and ack are all denied with forbidden
   - Expected: rep.reason equals `forbidden`
   - Expected: listed.reason equals `forbidden`
   - Expected: acked.reason equals `forbidden`
- No effect leaked: inbox empty, cursor unset
   - Expected: channel_inbox_count(store, "tenant-a", "mock-1") equals `0`
   - Expected: channel_cursor(store, "tenant-a", "mock-1") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("denies every hub operation on a killed channel with reason forbidden")
val store = fresh_store()
val t = tenant_a()
val a = admin()
val s = session_for(t, a)
step("Kill the channel")
val killed = channel_kill(store, s, t, a, "mock-1")
expect(killed.ok).to_be(true)
expect(channel_enabled(store, "tenant-a", "mock-1")).to_be(false)
step("Import, listing publish, and ack are all denied with forbidden")
val adapter = mock_channel(scripted_orders(), 2)
val rep = channel_import_orders(store, s, t, a, env("imp-1"), adapter, "mock-1", 10)
expect(rep.ok).to_be(false)
expect(rep.reason).to_equal("forbidden")
val listed = channel_list_product(store, s, t, a, adapter, "mock-1", "widget-1", Money(amount_cents: 500, currency: "USD"))
expect(listed.reason).to_equal("forbidden")
val acked = channel_ack_order(store, s, t, a, adapter, "mock-1", "ext-100")
expect(acked.reason).to_equal("forbidden")
step("No effect leaked: inbox empty, cursor unset")
expect(channel_inbox_count(store, "tenant-a", "mock-1")).to_equal(0)
expect(channel_cursor(store, "tenant-a", "mock-1")).to_equal("")
store_close(store)
```

</details>

### channel hub — listing mapping and acknowledge flow

#### maps sku to external listing id and acks an imported order once

- maps sku to external listing id and acks an imported order once
- Publish a listing — mapping row records the external id
   - Expected: channel_listing_external_id(store, "tenant-a", "mock-1", "widget-1") equals `ext-listing-widget-1`
- Import, then acknowledge one order
   - Expected: ack1.reason equals `accepted`
- A repeated ack is a recorded duplicate; an unknown order is not-found
   - Expected: ack2.reason equals `duplicate-key`
   - Expected: ack3.reason equals `not-found`
- A downed provider denies the ack without recording it
   - Expected: ack4.reason equals `store-error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps sku to external listing id and acks an imported order once")
val store = fresh_store()
val t = tenant_a()
val a = admin()
val s = session_for(t, a)
val adapter = mock_channel(scripted_orders(), 4)
step("Publish a listing — mapping row records the external id")
val listed = channel_list_product(store, s, t, a, adapter, "mock-1", "widget-1", Money(amount_cents: 500, currency: "USD"))
expect(listed.ok).to_be(true)
expect(channel_listing_external_id(store, "tenant-a", "mock-1", "widget-1")).to_equal("ext-listing-widget-1")
step("Import, then acknowledge one order")
channel_import_orders(store, s, t, a, env("imp-1"), adapter, "mock-1", 10)
val ack1 = channel_ack_order(store, s, t, a, adapter, "mock-1", "ext-100")
expect(ack1.ok).to_be(true)
expect(ack1.reason).to_equal("accepted")
step("A repeated ack is a recorded duplicate; an unknown order is not-found")
val ack2 = channel_ack_order(store, s, t, a, adapter, "mock-1", "ext-100")
expect(ack2.ok).to_be(true)
expect(ack2.reason).to_equal("duplicate-key")
val ack3 = channel_ack_order(store, s, t, a, adapter, "mock-1", "ext-999")
expect(ack3.reason).to_equal("not-found")
step("A downed provider denies the ack without recording it")
val ack4 = channel_ack_order(store, s, t, a, mock_channel_down([], 1), "mock-1", "ext-101")
expect(ack4.reason).to_equal("store-error")
store_close(store)
```

</details>

### channel hub — reconciliation

#### detects a seeded orphan, unacked orders, and checkpoint stats

- detects a seeded orphan, unacked orders, and checkpoint stats
- Import 4 orders plus one order for an UNKNOWN sku (rejected -> orphan inbox row)
- Ack one order, then reconcile
   - Expected: rep.inbox_total equals `5`
   - Expected: rep.imported_count equals `4`
   - Expected: rep.orphan_external_ids.len() equals `1`
   - Expected: rep.orphan_external_ids[0] equals `ext-900`
   - Expected: rep.unacked_external_ids.len() equals `3`
   - Expected: rep.checkpoints_recorded equals `1`
   - Expected: rep.last_cursor equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects a seeded orphan, unacked orders, and checkpoint stats")
val store = fresh_store()
val t = tenant_a()
val a = admin()
val s = session_for(t, a)
step("Import 4 orders plus one order for an UNKNOWN sku (rejected -> orphan inbox row)")
var orders = scripted_orders()
orders.push(ChannelOrder(external_id: "ext-900", sku: "no-such-sku", qty: 1))
val adapter = mock_channel(orders, 5)
channel_import_orders(store, s, t, a, env("imp-1"), adapter, "mock-1", 10)
step("Ack one order, then reconcile")
channel_ack_order(store, s, t, a, adapter, "mock-1", "ext-100")
val rep = channel_reconcile(store, "tenant-a", "mock-1")
expect(rep.inbox_total).to_equal(5)
expect(rep.imported_count).to_equal(4)
expect(rep.orphan_external_ids.len()).to_equal(1)
expect(rep.orphan_external_ids[0]).to_equal("ext-900")
expect(rep.unacked_external_ids.len()).to_equal(3)
expect(rep.checkpoints_recorded).to_equal(1)
expect(rep.last_cursor).to_equal("5")
store_close(store)
```

</details>

### channel hub — tenant isolation

#### imports, cursors, and reconciliation never cross tenants

- imports, cursors, and reconciliation never cross tenants
- Tenant B registers its own channel and catalog
- Tenant A imports; tenant B does not
   - Expected: channel_inbox_count(store, "tenant-a", "mock-1") equals `4`
   - Expected: channel_inbox_count(store, "tenant-b", "mock-1") equals `0`
   - Expected: channel_cursor(store, "tenant-b", "mock-1") equals ``
   - Expected: sale_available_stock(store, "tenant-b", "widget-1") equals `50`
- Tenant B's reconcile sees only its own (empty) state
   - Expected: rep.inbox_total equals `0`
   - Expected: rep.checkpoints_recorded equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("imports, cursors, and reconciliation never cross tenants")
val store = fresh_store()
val ta = tenant_a()
val a = admin()
val sa = session_for(ta, a)
step("Tenant B registers its own channel and catalog")
val tb = TenantContext(tenant_id: "tenant-b", name: "Tenant B")
val b = ActorContext(actor_id: "op-b", role: "admin")
val sb = SessionContext(token: "tok-b", actor_id: "op-b", tenant_id: "tenant-b", active: true)
sale_add_product(store, sb, tb, b, "widget-1", "Widget", Money(amount_cents: 700, currency: "USD"))
sale_receive_stock(store, sb, tb, b, "widget-1", 50)
channel_register(store, sb, tb, b, "mock-1", "mock")
step("Tenant A imports; tenant B does not")
channel_import_orders(store, sa, ta, a, env("imp-1"), mock_channel(scripted_orders(), 4), "mock-1", 10)
expect(channel_inbox_count(store, "tenant-a", "mock-1")).to_equal(4)
expect(channel_inbox_count(store, "tenant-b", "mock-1")).to_equal(0)
expect(channel_cursor(store, "tenant-b", "mock-1")).to_equal("")
expect(sale_available_stock(store, "tenant-b", "widget-1")).to_equal(50)
step("Tenant B's reconcile sees only its own (empty) state")
val rep = channel_reconcile(store, "tenant-b", "mock-1")
expect(rep.inbox_total).to_equal(0)
expect(rep.checkpoints_recorded).to_equal(0)
store_close(store)
```

</details>

### channel hub — restart survival

#### cursor, inbox, and dedup survive close and reopen

- cursor, inbox, and dedup survive close and reopen
- Open a file-backed store; import page 1 then hit a provider failure
   - Expected: channel_cursor(store, "tenant-a", "mock-1") equals `2`
- Reopen — cursor persisted; import resumes at 2 and completes without duplicates
   - Expected: channel_cursor(store2, "tenant-a", "mock-1") equals `2`
   - Expected: rep.imported equals `2`
   - Expected: rep.duplicates equals `0`
   - Expected: channel_inbox_count(store2, "tenant-a", "mock-1") equals `4`
   - Expected: sale_available_stock(store2, "tenant-a", "widget-1") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cursor, inbox, and dedup survive close and reopen")
dir_create_all("/tmp/simple_channel_spec")
val path = "/tmp/simple_channel_spec/restart_survival.db"
if file_exists(path):
    file_delete(path)
val t = tenant_a()
val a = admin()
val s = session_for(t, a)
step("Open a file-backed store; import page 1 then hit a provider failure")
val store = store_open(path)
sale_setup(store)
channel_setup(store)
sale_add_product(store, s, t, a, "widget-1", "Widget", Money(amount_cents: 500, currency: "USD"))
sale_receive_stock(store, s, t, a, "widget-1", 100)
channel_register(store, s, t, a, "mock-1", "mock")
channel_import_orders(store, s, t, a, env("imp-1"), mock_channel_failing(scripted_orders(), 2, "2"), "mock-1", 10)
expect(channel_cursor(store, "tenant-a", "mock-1")).to_equal("2")
store_close(store)
step("Reopen — cursor persisted; import resumes at 2 and completes without duplicates")
val store2 = store_open(path)
sale_setup(store2)
channel_setup(store2)
expect(channel_cursor(store2, "tenant-a", "mock-1")).to_equal("2")
val rep = channel_import_orders(store2, s, t, a, env("imp-2"), mock_channel(scripted_orders(), 2), "mock-1", 10)
expect(rep.imported).to_equal(2)
expect(rep.duplicates).to_equal(0)
expect(channel_inbox_count(store2, "tenant-a", "mock-1")).to_equal(4)
expect(sale_available_stock(store2, "tenant-a", "widget-1")).to_equal(90)
store_close(store2)
file_delete(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Design:** `doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md §8`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d32b583ebca80e691035cdfd462b1ecaad27e7a483a345755fe579c1e4abfcd9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d32b583ebca80e691035cdfd462b1ecaad27e7a483a345755fe579c1e4abfcd9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d32b583ebca80e691035cdfd462b1ecaad27e7a483a345755fe579c1e4abfcd9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 34 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pages scripted orders deterministically by cursor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports every external order as exactly one internal order via the cursor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_channel/channel_hub_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-running the import produces zero new internal effects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
