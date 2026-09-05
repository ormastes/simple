# Enterprise Store file backend — same API without sqlite

> Evidence that `std.enterprise_store` runs UNCHANGED on the pure-Simple file backend (`file_backend.spl`), the fallback `store_open` selects by composition when the `rt_sqlite_*` externs are unavailable (SimpleOS in-guest, lane `.spipe/simple_enterprise_suite` Goal Set v2, AC-17). Exercised here explicitly via `store_open_file` so it is proven on hosts where sqlite IS available too. Covered: open + format marker, records layer (idempotency, outbox, sha256 audit chain) through the same store API, buffered-commit all-or-nothing semantics, migration re-run no-op, value round-trip of separator characters, and restart survival with auto-detection by the verifying open.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Store file backend — same API without sqlite

Evidence that `std.enterprise_store` runs UNCHANGED on the pure-Simple file backend (`file_backend.spl`), the fallback `store_open` selects by composition when the `rt_sqlite_*` externs are unavailable (SimpleOS in-guest, lane `.spipe/simple_enterprise_suite` Goal Set v2, AC-17). Exercised here explicitly via `store_open_file` so it is proven on hosts where sqlite IS available too. Covered: open + format marker, records layer (idempotency, outbox, sha256 audit chain) through the same store API, buffered-commit all-or-nothing semantics, migration re-run no-op, value round-trip of separator characters, and restart survival with auto-detection by the verifying open.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Evidence that `std.enterprise_store` runs UNCHANGED on the pure-Simple
file backend (`file_backend.spl`), the fallback `store_open` selects by
composition when the `rt_sqlite_*` externs are unavailable (SimpleOS
in-guest, lane `.spipe/simple_enterprise_suite` Goal Set v2, AC-17).
Exercised here explicitly via `store_open_file` so it is proven on hosts
where sqlite IS available too. Covered: open + format marker, records
layer (idempotency, outbox, sha256 audit chain) through the same store
API, buffered-commit all-or-nothing semantics, migration re-run no-op,
value round-trip of separator characters, and restart survival with
auto-detection by the verifying open.

## Troubleshooting

- acid=false on the file backend is HONEST: raw begin/rollback do not
  undo appends; atomic multi-write is the BufferedUow layer.
- A blank or foreign file is never adopted: fb magic line absent →
  open/verify fail closed.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

Lane: .spipe/simple_enterprise_suite (Goal Set v2, AC-17).

## Scenarios

### enterprise store file backend — same API without sqlite

#### opens a fresh file store healthy, with honest non-ACID capability

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens a fresh file store healthy, with honest non-ACID capability
- Open the store on the pure-Simple file backend
   - Expected: store.open_ok is true
- Verify format marker and health
   - Expected: store_verify(store) equals ``
- Capability is honestly non-ACID at the raw uow layer
   - Expected: store_backend_acid(store) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("opens a fresh file store healthy, with honest non-ACID capability")
val path = fresh_path("fb_open.store")
step("Open the store on the pure-Simple file backend")
val store = store_open_file(path)
expect(store.open_ok).to_equal(true)
step("Verify format marker and health")
expect(store_verify(store)).to_equal("")
step("Capability is honestly non-ACID at the raw uow layer")
expect(store_backend_acid(store)).to_equal(false)
store_close(store)
```

</details>

#### runs the records layer (idempotency, outbox, audit chain) unchanged

- runs the records layer (idempotency, outbox, audit chain) unchanged
- Record an idempotency key with its result
   - Expected: idempotency_seen(store, "t1", "k1") is false
   - Expected: idempotency_record(store, "t1", "k1", "ok:42") is true
   - Expected: idempotency_seen(store, "t1", "k1") is true
   - Expected: idempotency_result(store, "t1", "k1") equals `ok:42`
- Append outbox events and read them back tenant-scoped
   - Expected: outbox_append(store, "t1", "order.placed", "o-1") is true
   - Expected: outbox_append(store, "t2", "order.placed", "other-tenant") is true
   - Expected: pending.len() equals `1`
- Append audit entries and verify the sha256 chain
   - Expected: audit_append(store, "t1", "alice", "order.place", "o-1") is true
   - Expected: audit_append(store, "t1", "alice", "order.pay", "o-1") is true
   - Expected: audit_verify_chain(store, "t1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs the records layer (idempotency, outbox, audit chain) unchanged")
val path = fresh_path("fb_records.store")
val store = store_open_file(path)
step("Record an idempotency key with its result")
expect(idempotency_seen(store, "t1", "k1")).to_equal(false)
expect(idempotency_record(store, "t1", "k1", "ok:42")).to_equal(true)
expect(idempotency_seen(store, "t1", "k1")).to_equal(true)
expect(idempotency_result(store, "t1", "k1")).to_equal("ok:42")
step("Append outbox events and read them back tenant-scoped")
expect(outbox_append(store, "t1", "order.placed", "o-1")).to_equal(true)
expect(outbox_append(store, "t2", "order.placed", "other-tenant")).to_equal(true)
val pending = outbox_pending(store, "t1")
expect(pending.len()).to_equal(1)
step("Append audit entries and verify the sha256 chain")
expect(audit_append(store, "t1", "alice", "order.place", "o-1")).to_equal(true)
expect(audit_append(store, "t1", "alice", "order.pay", "o-1")).to_equal(true)
expect(audit_verify_chain(store, "t1")).to_equal(true)
store_close(store)
```

</details>

#### round-trips values containing tabs, newlines, percent and equals

- round-trips values containing tabs, newlines, percent and equals
- Store a payload full of separator characters
   - Expected: outbox_append(store, "t1", "raw", nasty) is true
- Read it back byte-identical
   - Expected: pending[0].1 equals `nasty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips values containing tabs, newlines, percent and equals")
val path = fresh_path("fb_roundtrip.store")
val store = store_open_file(path)
val nasty = "a\tb\nc%09=d%e"
step("Store a payload full of separator characters")
expect(outbox_append(store, "t1", "raw", nasty)).to_equal(true)
step("Read it back byte-identical")
val pending = outbox_pending(store, "t1")
expect(pending[0].1).to_equal(nasty)
store_close(store)
```

</details>

#### applies a buffered commit all-or-nothing under an injected write failure

- applies a buffered commit all-or-nothing under an injected write failure
- Stage two writes and commit with an injected write failure
   - Expected: buffered_commit(store, uow, store_faults_failing_commit()) is false
- Nothing reached the store
   - Expected: outbox_pending(store, "t1").len() equals `0`
- The same commit without the fault applies both writes
   - Expected: buffered_commit(store, uow, store_faults_none()) is true
   - Expected: outbox_pending(store, "t1").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies a buffered commit all-or-nothing under an injected write failure")
val path = fresh_path("fb_buffered.store")
val store = store_open_file(path)
step("Stage two writes and commit with an injected write failure")
var uow = buffered_uow_new()
uow = buffered_write(uow, "INSERT INTO outbox (tenant_id, event_type, payload) VALUES (?, ?, ?)", ["t1", "e1", "p1"])
uow = buffered_write(uow, "INSERT INTO outbox (tenant_id, event_type, payload) VALUES (?, ?, ?)", ["t1", "e2", "p2"])
expect(buffered_commit(store, uow, store_faults_failing_commit())).to_equal(false)
step("Nothing reached the store")
expect(outbox_pending(store, "t1").len()).to_equal(0)
step("The same commit without the fault applies both writes")
expect(buffered_commit(store, uow, store_faults_none())).to_equal(true)
expect(outbox_pending(store, "t1").len()).to_equal(2)
store_close(store)
```

</details>

#### treats migrations as apply-once with re-run as a no-op

- treats migrations as apply-once with re-run as a no-op
- Apply a named migration
   - Expected: store_migration_applied(store, "m1") is false
   - Expected: store_migrate(store, "m1", "CREATE TABLE demo (id INTEGER PRIMARY KEY)") is true
   - Expected: store_migration_applied(store, "m1") is true
- Re-run is a no-op that still reports applied
   - Expected: store_migrate(store, "m1", "CREATE TABLE demo (id INTEGER PRIMARY KEY)") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats migrations as apply-once with re-run as a no-op")
val path = fresh_path("fb_migrate.store")
val store = store_open_file(path)
step("Apply a named migration")
expect(store_migration_applied(store, "m1")).to_equal(false)
expect(store_migrate(store, "m1", "CREATE TABLE demo (id INTEGER PRIMARY KEY)")).to_equal(true)
expect(store_migration_applied(store, "m1")).to_equal(true)
step("Re-run is a no-op that still reports applied")
expect(store_migrate(store, "m1", "CREATE TABLE demo (id INTEGER PRIMARY KEY)")).to_equal(true)
store_close(store)
```

</details>

#### survives restart and is auto-detected by the verifying open

- survives restart and is auto-detected by the verifying open
   - Expected: audit_append(store, "t1", "alice", "boot", "d") is true
- Reopen the same path through store_open_verified (no backend named)
   - Expected: reopened.1 equals ``
   - Expected: reopened.0.open_ok is true
- State and the audit chain survived the restart
   - Expected: audit_verify_chain(reopened.0, "t1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("survives restart and is auto-detected by the verifying open")
val path = fresh_path("fb_restart.store")
val store = store_open_file(path)
expect(audit_append(store, "t1", "alice", "boot", "d")).to_equal(true)
store_close(store)
step("Reopen the same path through store_open_verified (no backend named)")
val reopened = store_open_verified(path)
expect(reopened.1).to_equal("")
expect(reopened.0.open_ok).to_equal(true)
step("State and the audit chain survived the restart")
expect(audit_verify_chain(reopened.0, "t1")).to_equal(true)
store_close(reopened.0)
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
- **Research:** `doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1b1069d72799a43ae406297c80f275011104e8a78f77f640c60a79205522f889`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b1069d72799a43ae406297c80f275011104e8a78f77f640c60a79205522f889`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b1069d72799a43ae406297c80f275011104e8a78f77f640c60a79205522f889`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens a fresh file store healthy, with honest non-ACID capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the records layer (idempotency, outbox, audit chain) unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_file_backend_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips values containing tabs, newlines, percent and equals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
