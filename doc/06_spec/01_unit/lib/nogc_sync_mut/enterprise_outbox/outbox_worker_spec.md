# Enterprise Outbox Worker — dispatch and reconciliation

> Specs for `std.enterprise_outbox` (sync-tier impl `src/lib/nogc_sync_mut/enterprise_outbox/outbox_worker.spl`): outbox dispatch with at-least-once semantics over the insert-only enterprise store, and reconciliation reporting (dead-letter candidates, dispatch corruption) as data.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Outbox Worker — dispatch and reconciliation

Specs for `std.enterprise_outbox` (sync-tier impl `src/lib/nogc_sync_mut/enterprise_outbox/outbox_worker.spl`): outbox dispatch with at-least-once semantics over the insert-only enterprise store, and reconciliation reporting (dead-letter candidates, dispatch corruption) as data.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_outbox/outbox_worker_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Specs for `std.enterprise_outbox` (sync-tier impl
`src/lib/nogc_sync_mut/enterprise_outbox/outbox_worker.spl`): outbox
dispatch with at-least-once semantics over the insert-only enterprise
store, and reconciliation reporting (dead-letter candidates, dispatch
corruption) as data.

Delivery contract under test: a dispatch is recorded as a NEW
`outbox_dispatch` row keyed by the outbox row id (no UPDATE); pending =
rows minus dispatch records, filtered in pure Simple. Exactly-once EFFECT
belongs to the consumer via the outbox-row-id dedup key; within one store
a re-run yields exactly one dispatch record per row.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W2-F, outbox/reconciliation §5/§8).

## Scenarios

### outbox worker — dispatch happy path

#### dispatches all pending events and writes audit entries

- Append three outbox events for tenant A
   - Expected: outbox_worker_pending(store, "tenant-a").len() equals `3`
- Dispatch a full batch to an accepting target
   - Expected: rep.attempted equals `3`
   - Expected: rep.dispatched equals `3`
   - Expected: rep.failed equals `0`
- All rows dispatched, audit chain intact with one entry per dispatch
   - Expected: outbox_worker_pending(store, "tenant-a").len() equals `0`
   - Expected: dispatch_rows(store, "tenant-a") equals `3`
   - Expected: audits equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store()
step("Append three outbox events for tenant A")
outbox_append(store, "tenant-a", "sales.order.created", "o1")
outbox_append(store, "tenant-a", "sales.order.paid", "o1")
outbox_append(store, "tenant-a", "inventory.stock.reserved", "o1")
expect(outbox_worker_pending(store, "tenant-a").len()).to_equal(3)
step("Dispatch a full batch to an accepting target")
val rep = outbox_dispatch_batch(store, "tenant-a", dispatch_target_ok(), 1000, 10)
expect(rep.attempted).to_equal(3)
expect(rep.dispatched).to_equal(3)
expect(rep.failed).to_equal(0)
step("All rows dispatched, audit chain intact with one entry per dispatch")
expect(outbox_worker_pending(store, "tenant-a").len()).to_equal(0)
expect(dispatch_rows(store, "tenant-a")).to_equal(3)
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
var audits = 0
for row in store_rows(store, "audit_log", "id, tenant_id, actor, action, detail, prev_hash, hash"):
    if sqlite_row_get(row, "tenant_id") == "tenant-a" and sqlite_row_get(row, "action") == "outbox.dispatch":
        audits = audits + 1
expect(audits).to_equal(3)
store_close(store)
```

</details>

### outbox worker — at-least-once on handler failure

#### leaves rows pending and records the retry when the handler fails

- Dispatch to an always-failing target
   - Expected: rep.attempted equals `1`
   - Expected: rep.dispatched equals `0`
   - Expected: rep.failed equals `1`
- The row is still pending and one retry row is recorded
   - Expected: pending.len() equals `1`
   - Expected: outbox_retry_count(store, "tenant-a", pending[0].outbox_id) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store()
outbox_append(store, "tenant-a", "sales.order.created", "o1")
step("Dispatch to an always-failing target")
val rep = outbox_dispatch_batch(store, "tenant-a", dispatch_target_failing(), 1000, 10)
expect(rep.attempted).to_equal(1)
expect(rep.dispatched).to_equal(0)
expect(rep.failed).to_equal(1)
step("The row is still pending and one retry row is recorded")
val pending = outbox_worker_pending(store, "tenant-a")
expect(pending.len()).to_equal(1)
expect(outbox_retry_count(store, "tenant-a", pending[0].outbox_id)).to_equal(1)
store_close(store)
```

</details>

### outbox worker — partial batch and replay dedup

#### records successes, keeps failures pending, and never double-dispatches on re-run

- Append three events; the middle payload will be rejected
- Dispatch with a target that fails payload p-bad
   - Expected: rep1.dispatched equals `2`
   - Expected: rep1.failed equals `1`
   - Expected: outbox_worker_pending(store, "tenant-a").len() equals `1`
- Re-run with an accepting target — replay dispatches ONLY the pending row
   - Expected: rep2.attempted equals `1`
   - Expected: rep2.dispatched equals `1`
- Exactly one dispatch record per outbox row — dedup by outbox row id
   - Expected: dispatch_rows(store, "tenant-a") equals `3`
   - Expected: outbox_worker_pending(store, "tenant-a").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store()
step("Append three events; the middle payload will be rejected")
outbox_append(store, "tenant-a", "e.one", "p1")
outbox_append(store, "tenant-a", "e.two", "p-bad")
outbox_append(store, "tenant-a", "e.three", "p3")
step("Dispatch with a target that fails payload p-bad")
val rep1 = outbox_dispatch_batch(store, "tenant-a", dispatch_target_failing_payload("p-bad"), 1000, 10)
expect(rep1.dispatched).to_equal(2)
expect(rep1.failed).to_equal(1)
expect(outbox_worker_pending(store, "tenant-a").len()).to_equal(1)
step("Re-run with an accepting target — replay dispatches ONLY the pending row")
val rep2 = outbox_dispatch_batch(store, "tenant-a", dispatch_target_ok(), 1001, 10)
expect(rep2.attempted).to_equal(1)
expect(rep2.dispatched).to_equal(1)
step("Exactly one dispatch record per outbox row — dedup by outbox row id")
expect(dispatch_rows(store, "tenant-a")).to_equal(3)
expect(outbox_worker_pending(store, "tenant-a").len()).to_equal(0)
store_close(store)
```

</details>

#### honors max_batch and picks up the remainder next run

- Dispatch with max_batch=2
   - Expected: rep1.attempted equals `2`
   - Expected: outbox_worker_pending(store, "tenant-a").len() equals `1`
- Second run drains the remainder without duplicates
   - Expected: rep2.dispatched equals `1`
   - Expected: dispatch_rows(store, "tenant-a") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store()
outbox_append(store, "tenant-a", "e.one", "p1")
outbox_append(store, "tenant-a", "e.two", "p2")
outbox_append(store, "tenant-a", "e.three", "p3")
step("Dispatch with max_batch=2")
val rep1 = outbox_dispatch_batch(store, "tenant-a", dispatch_target_ok(), 1000, 2)
expect(rep1.attempted).to_equal(2)
expect(outbox_worker_pending(store, "tenant-a").len()).to_equal(1)
step("Second run drains the remainder without duplicates")
val rep2 = outbox_dispatch_batch(store, "tenant-a", dispatch_target_ok(), 1001, 2)
expect(rep2.dispatched).to_equal(1)
expect(dispatch_rows(store, "tenant-a")).to_equal(3)
store_close(store)
```

</details>

### outbox worker — reconciliation

#### flags a row as dead-letter after more than N recorded failures

- Fail delivery three times
- Reconcile with max_retries=2 — the row is a dead-letter candidate
   - Expected: rep.pending_count equals `1`
   - Expected: rep.dead_letter_ids.len() equals `1`
   - Expected: rep.orphan_dispatch_ids.len() equals `0`
- With max_retries=5 it is pending but not dead-lettered
   - Expected: rep2.dead_letter_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store()
outbox_append(store, "tenant-a", "e.doomed", "p-bad")
step("Fail delivery three times")
outbox_dispatch_batch(store, "tenant-a", dispatch_target_failing(), 1000, 10)
outbox_dispatch_batch(store, "tenant-a", dispatch_target_failing(), 1001, 10)
outbox_dispatch_batch(store, "tenant-a", dispatch_target_failing(), 1002, 10)
step("Reconcile with max_retries=2 — the row is a dead-letter candidate")
val rep = reconcile_report(store, "tenant-a", 2)
expect(rep.pending_count).to_equal(1)
expect(rep.dead_letter_ids.len()).to_equal(1)
expect(rep.orphan_dispatch_ids.len()).to_equal(0)
step("With max_retries=5 it is pending but not dead-lettered")
val rep2 = reconcile_report(store, "tenant-a", 5)
expect(rep2.dead_letter_ids.len()).to_equal(0)
store_close(store)
```

</details>

#### reports a dispatch record without an outbox row as corruption

- Forge a dispatch record for a nonexistent outbox row id
- Reconcile detects the orphan and keeps counts honest
   - Expected: rep.total_rows equals `1`
   - Expected: rep.dispatched_count equals `1`
   - Expected: rep.orphan_dispatch_ids.len() equals `1`
   - Expected: rep.orphan_dispatch_ids[0] equals `999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store()
outbox_append(store, "tenant-a", "e.one", "p1")
outbox_dispatch_batch(store, "tenant-a", dispatch_target_ok(), 1000, 10)
step("Forge a dispatch record for a nonexistent outbox row id")
store_insert_row(store,
    "INSERT INTO outbox_dispatch (tenant_id, outbox_id, dispatched_at) VALUES (?, ?, ?)",
    ["tenant-a", "999999", "1000"])
step("Reconcile detects the orphan and keeps counts honest")
val rep = reconcile_report(store, "tenant-a", 3)
expect(rep.total_rows).to_equal(1)
expect(rep.dispatched_count).to_equal(1)
expect(rep.orphan_dispatch_ids.len()).to_equal(1)
expect(rep.orphan_dispatch_ids[0]).to_equal("999999")
store_close(store)
```

</details>

### outbox worker — tenant isolation

#### dispatch and reconciliation never cross tenants

- Dispatch tenant A only
   - Expected: outbox_worker_pending(store, "tenant-a").len() equals `0`
   - Expected: outbox_worker_pending(store, "tenant-b").len() equals `1`
- Tenant B's reconcile sees only its own row
   - Expected: rep.total_rows equals `1`
   - Expected: rep.pending_count equals `1`
   - Expected: rep.dispatched_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store()
outbox_append(store, "tenant-a", "e.a", "pa")
outbox_append(store, "tenant-b", "e.b", "pb")
step("Dispatch tenant A only")
outbox_dispatch_batch(store, "tenant-a", dispatch_target_ok(), 1000, 10)
expect(outbox_worker_pending(store, "tenant-a").len()).to_equal(0)
expect(outbox_worker_pending(store, "tenant-b").len()).to_equal(1)
step("Tenant B's reconcile sees only its own row")
val rep = reconcile_report(store, "tenant-b", 3)
expect(rep.total_rows).to_equal(1)
expect(rep.pending_count).to_equal(1)
expect(rep.dispatched_count).to_equal(0)
store_close(store)
```

</details>

### outbox worker — restart survival

#### pending and dispatch state survive close and reopen

- Open a file-backed store, append two events, dispatch one
   - Expected: outbox_worker_pending(store, "tenant-a").len() equals `1`
- Reopen — exactly the failed row is still pending, dispatch survives
   - Expected: pending.len() equals `1`
   - Expected: pending[0].payload equals `p-bad`
   - Expected: dispatch_rows(store2, "tenant-a") equals `1`
- Draining after restart yields exactly one dispatch record per row
   - Expected: dispatch_rows(store2, "tenant-a") equals `2`
   - Expected: outbox_worker_pending(store2, "tenant-a").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("/tmp/simple_outbox_spec")
val path = "/tmp/simple_outbox_spec/restart_survival.db"
if file_exists(path):
    file_delete(path)
step("Open a file-backed store, append two events, dispatch one")
val store = store_open(path)
outbox_worker_setup(store)
outbox_append(store, "tenant-a", "e.one", "p1")
outbox_append(store, "tenant-a", "e.two", "p-bad")
outbox_dispatch_batch(store, "tenant-a", dispatch_target_failing_payload("p-bad"), 1000, 10)
expect(outbox_worker_pending(store, "tenant-a").len()).to_equal(1)
store_close(store)
step("Reopen — exactly the failed row is still pending, dispatch survives")
val store2 = store_open(path)
outbox_worker_setup(store2)
val pending = outbox_worker_pending(store2, "tenant-a")
expect(pending.len()).to_equal(1)
expect(pending[0].payload).to_equal("p-bad")
expect(dispatch_rows(store2, "tenant-a")).to_equal(1)
step("Draining after restart yields exactly one dispatch record per row")
outbox_dispatch_batch(store2, "tenant-a", dispatch_target_ok(), 2000, 10)
expect(dispatch_rows(store2, "tenant-a")).to_equal(2)
expect(outbox_worker_pending(store2, "tenant-a").len()).to_equal(0)
store_close(store2)
file_delete(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
