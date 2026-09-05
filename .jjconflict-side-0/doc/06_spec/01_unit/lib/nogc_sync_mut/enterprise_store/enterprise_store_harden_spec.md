# Enterprise Store hardening — corruption detection and write-failure commits

> Failure-path evidence for `std.enterprise_store` (lane `.spipe/simple_enterprise_suite`, AC-18). Two families:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- verifies a freshly opened store as healthy
- Open a normal store and verify it
   - Expected: store_verify(store) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("verifies a freshly opened store as healthy")
step("Open a normal store and verify it")
val store = store_open(":memory:")
expect(store_verify(store)).to_equal("")
store_close(store)
```

</details>

#### rejects a blank non-store file with an explicit error on verified open

- rejects a blank non-store file with an explicit error on verified open
- Create a blank file that is not an enterprise store
- Open it with the verifying open
- Verify it is rejected, never silently accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a blank non-store file with an explicit error on verified open")
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

- rejects a bad-magic (garbage bytes) store file with an explicit error
- Write garbage bytes where a store should be
- Open it with the verifying open
- Verify the tampered store is detected with an explicit error


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a bad-magic (garbage bytes) store file with an explicit error")
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

- commits a healthy buffered unit of work with all effects visible
- Stage a domain write, an outbox event, and an idempotency key
- Commit with no injected fault
- Verify both effects are observable
   - Expected: outbox_pending(store, "tenant-a").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("commits a healthy buffered unit of work with all effects visible")
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

- surfaces an injected disk-full write failure as a failed commit with zero partial effects
- Stage the same writes on a fresh store
- Commit with the failing-write fault injected
- Verify the commit failed
- Verify NO partial effects are observable — neither staged write landed
   - Expected: outbox_pending(store, "tenant-a").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("surfaces an injected disk-full write failure as a failed commit with zero partial effects")
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

### enterprise store harden — raw transaction atomicity, gated on the live ACID probe

#### rolls back a multi-row transaction with zero survivors when the backend is ACID

- rolls back a multi-row transaction with zero survivors when the backend is ACID
- Read the live backend capability probe
- Write two rows inside one raw transaction and roll it back
- Backend is ACID — the rollback must have removed BOTH rows
   - Expected: survivors equals `0`
- Backend is NOT ACID (interpreter rt_sqlite emulation) — both rows must survive, the honest negative
   - Expected: survivors equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rolls back a multi-row transaction with zero survivors when the backend is ACID")
# This is the assertion the suite could not carry until 2026-08-17.
# It is GATED on store_backend_acid(), a live probe, not on a build
# flag: whichever branch runs, it asserts a definite number, so the
# scenario can never pass by doing nothing.
#
# - Real SQLite (AOT `--native`, links libsqlite3): probe true, both
#   rows must be gone.
# - Interpreter rt_sqlite emulation (`bin/simple test`): probe false,
#   raw ROLLBACK is a no-op, so both rows MUST still be there. The
#   emulation is not silently tolerated — it is pinned to its exact
#   non-ACID behaviour, and drift in either direction fails loudly.
#   Atomic multi-write on that backend is BufferedUow, covered above.
val store = store_open(":memory:")
step("Read the live backend capability probe")
val acid = store_backend_acid(store)
step("Write two rows inside one raw transaction and roll it back")
uow_begin(store)
outbox_append(store, "tenant-tx", "sales.order.created", "o1")
outbox_append(store, "tenant-tx", "sales.order.created", "o2")
uow_rollback(store)
val survivors = outbox_pending(store, "tenant-tx").len()
if acid:
    step("Backend is ACID — the rollback must have removed BOTH rows")
    expect(survivors).to_equal(0)
else:
    step("Backend is NOT ACID (interpreter rt_sqlite emulation) — both rows must survive, the honest negative")
    expect(survivors).to_equal(2)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d9b7f5df9aaefda6d1f9401332c218848fb6ad7d2d3a386a63d04ff6b31f5c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d9b7f5df9aaefda6d1f9401332c218848fb6ad7d2d3a386a63d04ff6b31f5c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d9b7f5df9aaefda6d1f9401332c218848fb6ad7d2d3a386a63d04ff6b31f5c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies a freshly opened store as healthy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a blank non-store file with an explicit error on verified open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_harden_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a bad-magic (garbage bytes) store file with an explicit error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
