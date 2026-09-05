# Enterprise Store — write-failure recovery, file backend (W14-B)

> Crash-consistency evidence for `std.enterprise_store` (lane `.spipe/simple_enterprise_suite`, DB hardening W14-B). Using the `StoreFaults` + `BufferedUow` composition seam, a write failure mid-unit-of-work must leave the store CONSISTENT:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Store — write-failure recovery, file backend (W14-B)

Crash-consistency evidence for `std.enterprise_store` (lane `.spipe/simple_enterprise_suite`, DB hardening W14-B). Using the `StoreFaults` + `BufferedUow` composition seam, a write failure mid-unit-of-work must leave the store CONSISTENT:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_write_failure_recovery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Crash-consistency evidence for `std.enterprise_store` (lane
`.spipe/simple_enterprise_suite`, DB hardening W14-B). Using the
`StoreFaults` + `BufferedUow` composition seam, a write failure mid-unit-of-work
must leave the store CONSISTENT:

1. the partial effect is NOT durably visible (asserted after CLOSE + REOPEN, so
   this is a real durability claim, not an in-process read);
2. the idempotency key is NOT consumed, so an operator-driven retry of the whole
   command succeeds EXACTLY ONCE (a third attempt is detected as a replay).

Backend: the **file backend** (SPLSTORE1), the durable path. The interpreter
`rt_sqlite_*` externs are a non-ACID, non-persistent emulation
(doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md),
so a durable-visibility claim is only honest against the on-disk file backend.
The complementary :memory: zero-partial-effect proof lives in
enterprise_store_harden_spec.spl.

## Troubleshooting

- retry did not succeed / key already consumed — a failed buffered_commit must
  apply NOTHING; check buffered_commit short-circuits before the first write.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W14-B).

## Scenarios

### enterprise store — write-failure recovery on the durable file backend

#### a failed commit consumes no idempotency key and leaves nothing durable; retry succeeds exactly once

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a failed commit consumes no idempotency key and leaves nothing durable; retry succeeds exactly once
- Attempt 1: commit the command with an injected disk-full write failure
- In-process: neither the key nor the outbox event landed
   - Expected: outbox_pending(s1, "tenant-a").len() equals `0`
- Durability: reopen the on-disk store — the failed attempt persisted nothing
   - Expected: outbox_pending(s2, "tenant-a").len() equals `0`
- Attempt 2 (operator retry): the key was never consumed, so the retry applies
   - Expected: idempotency_result(s2, "tenant-a", "ord-1") equals `accepted`
   - Expected: outbox_pending(s2, "tenant-a").len() equals `1`
- Exactly once: a third attempt is a replay — the guard skips re-applying
- Durable outbox still holds exactly one event — no duplicate side effect
   - Expected: outbox_pending(s3, "tenant-a").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a failed commit consumes no idempotency key and leaves nothing durable; retry succeeds exactly once")
val path = "build/test-artifacts/enterprise_write_failure_recovery.db"
fresh(path)

step("Attempt 1: commit the command with an injected disk-full write failure")
val s1 = store_open_file(path)
expect(s1.open_ok).to_be(true)
val ok1 = buffered_commit(s1, stage_command(), store_faults_failing_commit())
expect(ok1).to_be(false)
step("In-process: neither the key nor the outbox event landed")
expect(idempotency_seen(s1, "tenant-a", "ord-1")).to_be(false)
expect(outbox_pending(s1, "tenant-a").len()).to_equal(0)
store_close(s1)

step("Durability: reopen the on-disk store — the failed attempt persisted nothing")
val s2 = store_open_file(path)
expect(idempotency_seen(s2, "tenant-a", "ord-1")).to_be(false)
expect(outbox_pending(s2, "tenant-a").len()).to_equal(0)

step("Attempt 2 (operator retry): the key was never consumed, so the retry applies")
val ok2 = buffered_commit(s2, stage_command(), store_faults_none())
expect(ok2).to_be(true)
expect(idempotency_seen(s2, "tenant-a", "ord-1")).to_be(true)
expect(idempotency_result(s2, "tenant-a", "ord-1")).to_equal("accepted")
expect(outbox_pending(s2, "tenant-a").len()).to_equal(1)
store_close(s2)

step("Exactly once: a third attempt is a replay — the guard skips re-applying")
val s3 = store_open_file(path)
val replay = idempotency_seen(s3, "tenant-a", "ord-1")
expect(replay).to_be(true)
if not replay:
    buffered_commit(s3, stage_command(), store_faults_none())
step("Durable outbox still holds exactly one event — no duplicate side effect")
expect(outbox_pending(s3, "tenant-a").len()).to_equal(1)
store_close(s3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `fa28449871ad8647236d31faa6ed8d28adbd9090ecca45d62850c9e3623994f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa28449871ad8647236d31faa6ed8d28adbd9090ecca45d62850c9e3623994f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa28449871ad8647236d31faa6ed8d28adbd9090ecca45d62850c9e3623994f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_write_failure_recovery_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_write_failure_recovery_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_write_failure_recovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_write_failure_recovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_write_failure_recovery_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_write_failure_recovery_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a failed commit consumes no idempotency key and leaves nothing durable; retry succeeds exactly once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
