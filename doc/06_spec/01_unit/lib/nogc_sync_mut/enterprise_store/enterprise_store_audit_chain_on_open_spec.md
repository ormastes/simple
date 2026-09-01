# Enterprise Store — audit-chain tamper detection ON OPEN (W14-B)

> Crash-consistency / tamper-detection evidence for `std.enterprise_store` (lane `.spipe/simple_enterprise_suite`, DB hardening W14-B). The store keeps a sha256-chained append-only audit log (records.spl); `audit_verify_chain` recomputes it, but only when a caller explicitly asks. This spec pins the stronger guarantee: `store_open_verified` / `store_verify` re-walk the chain on the OPEN path and REJECT a store whose audit record was mutated out-of-band — so tampering is caught at open, not only on an explicit verify call.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Store — audit-chain tamper detection ON OPEN (W14-B)

Crash-consistency / tamper-detection evidence for `std.enterprise_store` (lane `.spipe/simple_enterprise_suite`, DB hardening W14-B). The store keeps a sha256-chained append-only audit log (records.spl); `audit_verify_chain` recomputes it, but only when a caller explicitly asks. This spec pins the stronger guarantee: `store_open_verified` / `store_verify` re-walk the chain on the OPEN path and REJECT a store whose audit record was mutated out-of-band — so tampering is caught at open, not only on an explicit verify call.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_chain_on_open_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Crash-consistency / tamper-detection evidence for `std.enterprise_store`
(lane `.spipe/simple_enterprise_suite`, DB hardening W14-B). The store keeps a
sha256-chained append-only audit log (records.spl); `audit_verify_chain`
recomputes it, but only when a caller explicitly asks. This spec pins the
stronger guarantee: `store_open_verified` / `store_verify` re-walk the chain on
the OPEN path and REJECT a store whose audit record was mutated out-of-band —
so tampering is caught at open, not only on an explicit verify call.

Backend: the **file backend** (SPLSTORE1). Durability claims are based on this
path because the interpreter `rt_sqlite_*` externs are a non-ACID, non-persistent
emulation (doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md);
a real on-disk file is the only thing we can tamper with out-of-band and reopen.

## Troubleshooting

- open accepted a tampered store — `store_verify` is not re-walking the audit
  chain; wire `store_audit_chain_error` into the verify path.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W14-B).

## Scenarios

### enterprise store — audit chain verified on open (file backend)

#### accepts an untampered file-backend store with a valid audit chain

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts an untampered file-backend store with a valid audit chain
- Open the file backend and append two chained audit records
- Sanity: the persisted chain verifies before any tampering
- A verifying open accepts the healthy store
   - Expected: opened.1 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts an untampered file-backend store with a valid audit chain")
val path = "build/test-artifacts/enterprise_audit_chain_ok.db"
fresh_store(path)
step("Open the file backend and append two chained audit records")
val store = store_open_file(path)
expect(store.open_ok).to_be(true)
expect(audit_append(store, "t1", "alice", "login", "ok")).to_be(true)
expect(audit_append(store, "t1", "alice", "update", "row-7")).to_be(true)
store_close(store)
step("Sanity: the persisted chain verifies before any tampering")
val reopened = store_open_file(path)
expect(audit_verify_chain(reopened, "t1")).to_be(true)
store_close(reopened)
step("A verifying open accepts the healthy store")
val opened = store_open_verified(path)
expect(opened.0.open_ok).to_be(true)
expect(opened.1).to_equal("")
```

</details>

#### REJECTS on open a store whose audit payload was mutated out-of-band

- REJECTS on open a store whose audit payload was mutated out-of-band
- Persist a two-record audit chain to the file backend
- Tamper: mutate the first record's persisted detail out-of-band
- The stored hash no longer matches the mutated payload
- The verifying open MUST reject the tampered store


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REJECTS on open a store whose audit payload was mutated out-of-band")
val path = "build/test-artifacts/enterprise_audit_chain_tampered.db"
fresh_store(path)
step("Persist a two-record audit chain to the file backend")
val store = store_open_file(path)
expect(audit_append(store, "t1", "alice", "login", "ok")).to_be(true)
expect(audit_append(store, "t1", "alice", "update", "row-7")).to_be(true)
store_close(store)
step("Tamper: mutate the first record's persisted detail out-of-band")
val raw = file_read(path)
expect(raw.contains("detail=ok")).to_be(true)
expect(file_write(path, raw.replace("detail=ok", "detail=HACKED"))).to_be(true)
step("The stored hash no longer matches the mutated payload")
val tampered = store_open_file(path)
expect(audit_verify_chain(tampered, "t1")).to_be(false)
store_close(tampered)
step("The verifying open MUST reject the tampered store")
val opened = store_open_verified(path)
expect(opened.0.open_ok).to_be(false)
expect(opened.1.contains("corrupt store")).to_be(true)
expect(opened.1.contains("audit chain")).to_be(true)
```

</details>

#### REJECTS on open a store whose audit chain HASH was mutated out-of-band

- REJECTS on open a store whose audit chain HASH was mutated out-of-band
- Persist an audit record, then corrupt only its stored hash
- Corrupt the stored hash column (the leading tab pins the real hash column, never prev_hash)
- store_verify on the reopened file backend must flag the chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REJECTS on open a store whose audit chain HASH was mutated out-of-band")
val path = "build/test-artifacts/enterprise_audit_hash_tampered.db"
fresh_store(path)
step("Persist an audit record, then corrupt only its stored hash")
val store = store_open_file(path)
expect(audit_append(store, "t1", "bob", "delete", "acct-9")).to_be(true)
store_close(store)
val raw = file_read(path)
step("Corrupt the stored hash column (the leading tab pins the real hash column, never prev_hash)")
expect(raw.contains("\thash=")).to_be(true)
val corrupt = raw.replace("\thash=", "\thash=deadbeef")
expect(file_write(path, corrupt)).to_be(true)
step("store_verify on the reopened file backend must flag the chain")
val reopened = store_open_file(path)
val err = store_verify(reopened)
store_close(reopened)
expect(err.contains("corrupt store")).to_be(true)
expect(err.contains("audit chain")).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `b6154432678dd900e9520af64a41a2d4013260659fc271c6af6159fc7587df0f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6154432678dd900e9520af64a41a2d4013260659fc271c6af6159fc7587df0f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6154432678dd900e9520af64a41a2d4013260659fc271c6af6159fc7587df0f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_chain_on_open_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_chain_on_open_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_chain_on_open_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_chain_on_open_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_chain_on_open_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an untampered file-backend store with a valid audit chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_chain_on_open_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REJECTS on open a store whose audit payload was mutated out-of-band' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_audit_chain_on_open_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REJECTS on open a store whose audit chain HASH was mutated out-of-band' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
