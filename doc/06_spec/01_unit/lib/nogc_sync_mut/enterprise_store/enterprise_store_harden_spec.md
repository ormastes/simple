# Enterprise Store hardening — corruption detection and write-failure commits

> Failure-path evidence for `std.enterprise_store` (lane `.spipe/simple_enterprise_suite`, AC-18). Two families:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Store hardening — corruption detection and write-failure commits

Failure-path evidence for `std.enterprise_store` (lane `.spipe/simple_enterprise_suite`, AC-18). Two families:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Failure-path evidence for `std.enterprise_store` (lane
`.spipe/simple_enterprise_suite`, AC-18). Two families:

1. **Corruption detection** — a tampered or truncated store (missing system
   table, blank/bad-magic file) is detected on open/verify with an explicit
   error naming the table; it is never silently accepted.
2. **Write-failure commits** — a disk-full/short-write during commit surfaces
   as a FAILED commit with zero partial observable effects. The interpreter's
   rt_sqlite externs are a non-ACID emulation
   (doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md),
   so the failure is injected through the store's composition seam
   (`StoreFaults` + `BufferedUow`): writes are staged in pure Simple and
   applied all-or-nothing, which holds on BOTH backends.

## Troubleshooting

- `store_verify != ""` — the returned text names the first missing/unreadable
  system table; restore from backup, do not proceed.
- `buffered_commit == false` — no staged write was applied; retry the whole
  command, never resume mid-batch.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (Goal Set v2, AC-18).

## Scenarios

### enterprise store harden — corruption detection

#### verifies a freshly opened store as healthy

- Open a normal store and verify it
   - Expected: store_verify(store) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a normal store and verify it")
val store = store_open(":memory:")
expect(store_verify(store)).to_equal("")
store_close(store)
```

</details>

#### rejects a blank non-store file with an explicit error on verified open

- Create a blank file that is not an enterprise store
- Open it with the verifying open
- Verify it is rejected, never silently accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "build/test-artifacts/enterprise_harden_blank.db"
step("Create a blank file that is not an enterprise store")
dir_create_all("build/test-artifacts")
if file_exists(db_path):
    file_delete(db_path)
file_write(db_path, "")
step("Open it with the verifying open")
val opened = store_open_verified(db_path)
step("Verify it is rejected, never silently accepted")
expect(opened.0.open_ok).to_be(false)
expect(opened.1.contains("corrupt store")).to_be(true)
expect(opened.1.contains("schema_migrations")).to_be(true)
```

</details>

#### rejects a bad-magic (garbage bytes) store file with an explicit error

- Write garbage bytes where a store should be
- Open it with the verifying open
- Verify the tampered store is detected with an explicit error


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "build/test-artifacts/enterprise_harden_badmagic.db"
step("Write garbage bytes where a store should be")
dir_create_all("build/test-artifacts")
if file_exists(db_path):
    file_delete(db_path)
file_write(db_path, "NOT-A-SQLITE-DATABASE garbage bytes 12345")
step("Open it with the verifying open")
val opened = store_open_verified(db_path)
step("Verify the tampered store is detected with an explicit error")
expect(opened.0.open_ok).to_be(false)
expect(opened.1.contains("corrupt store")).to_be(true)
```

</details>

### enterprise store harden — write-failure commit (injected seam)

#### commits a healthy buffered unit of work with all effects visible

- Stage a domain write, an outbox event, and an idempotency key
- Commit with no injected fault
- Verify both effects are observable
   - Expected: outbox_pending(store, "tenant-a").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stage a domain write, an outbox event, and an idempotency key")
val store = store_open(":memory:")
var uow = buffered_uow_new()
uow = buffered_write(uow,
    "INSERT INTO outbox (tenant_id, event_type, payload) VALUES (?, ?, ?)",
    ["tenant-a", "sales.order.created", "o1"])
uow = buffered_write(uow,
    "INSERT INTO idempotency_keys (tenant_id, idem_key, result) VALUES (?, ?, ?)",
    ["tenant-a", "ord-1", "accepted"])
step("Commit with no injected fault")
val ok = buffered_commit(store, uow, store_faults_none())
expect(ok).to_be(true)
step("Verify both effects are observable")
expect(outbox_pending(store, "tenant-a").len()).to_equal(1)
expect(idempotency_seen(store, "tenant-a", "ord-1")).to_be(true)
store_close(store)
```

</details>

#### surfaces an injected disk-full write failure as a failed commit with zero partial effects

- Stage the same writes on a fresh store
- Commit with the failing-write fault injected
- Verify the commit failed
- Verify NO partial effects are observable — neither staged write landed
   - Expected: outbox_pending(store, "tenant-a").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stage the same writes on a fresh store")
val store = store_open(":memory:")
var uow = buffered_uow_new()
uow = buffered_write(uow,
    "INSERT INTO outbox (tenant_id, event_type, payload) VALUES (?, ?, ?)",
    ["tenant-a", "sales.order.created", "o1"])
uow = buffered_write(uow,
    "INSERT INTO idempotency_keys (tenant_id, idem_key, result) VALUES (?, ?, ?)",
    ["tenant-a", "ord-1", "accepted"])
step("Commit with the failing-write fault injected")
val ok = buffered_commit(store, uow, store_faults_failing_commit())
step("Verify the commit failed")
expect(ok).to_be(false)
step("Verify NO partial effects are observable — neither staged write landed")
expect(outbox_pending(store, "tenant-a").len()).to_equal(0)
expect(idempotency_seen(store, "tenant-a", "ord-1")).to_be(false)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
