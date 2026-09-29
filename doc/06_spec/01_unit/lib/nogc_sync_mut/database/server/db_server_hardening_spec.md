# Simple DB Server Tier — resource-bound hardening

> The server tier already fails closed on malformed frames, unknown ops and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple DB Server Tier — resource-bound hardening

The server tier already fails closed on malformed frames, unknown ops and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The server tier already fails closed on malformed frames, unknown ops and
capability misses.  This spec pins the RESOURCE bounds at the same trust
boundary: a well-formed, authenticated, authorized request stream must still
not be able to grow server state without limit.

| Bound | Guard |
|-------|-------|
| Open sessions per capsule | `MAX_OPEN_SESSIONS` — OPEN past the bound answers `ERR_LIMIT` |
| Overlay writes per transaction | `MAX_TXN_WRITES` — PUT/DEL past the bound answers `ERR_LIMIT` |

## Scenarios

### DB server tier — resource-bound hardening

#### still serves a valid session, write and read (control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- still serves a valid session, write and read (control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still serves a valid session, write and read (control)")
var server = make_server()
assert_contains(server.handle_message("OPEN as=alice credential=alice-secret"), "session=1")
assert_contains(server.handle_message("BEGIN session=1"), "OK")
assert_contains(server.handle_message("PUT session=1 tbl=users id=u1 name=ada"), "OK")
assert_contains(server.handle_message("GET session=1 tbl=users id=u1 col=name"), "value=ada")
```

</details>

#### refuses OPEN once the open-session bound is reached

- refuses OPEN once the open-session bound is reached


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses OPEN once the open-session bound is reached")
var server = make_server()
val capability = capability_with("alice", [grant_key("users", "read")])
var registry = server.registry
var i = 0
while i < MAX_OPEN_SESSIONS:
    registry.open_session("alice", capability)
    i = i + 1
server.registry = registry
val reply = server.handle_message("OPEN as=alice credential=alice-secret")
assert_contains(reply, "ERR")
assert_contains(reply, "code=limit")
```

</details>

#### allows OPEN again after sessions are closed

- allows OPEN again after sessions are closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows OPEN again after sessions are closed")
var server = make_server()
val capability = capability_with("alice", [grant_key("users", "read")])
var registry = server.registry
var i = 0
while i < MAX_OPEN_SESSIONS:
    val id = registry.open_session("alice", capability)
    registry.close_session(id)
    i = i + 1
server.registry = registry
assert_contains(server.handle_message("OPEN as=alice credential=alice-secret"), "session=")
```

</details>

#### refuses a write once the per-transaction overlay bound is reached

- refuses a write once the per-transaction overlay bound is reached


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a write once the per-transaction overlay bound is reached")
var server = make_server()
assert_contains(server.handle_message("OPEN as=alice credential=alice-secret"), "session=1")
assert_contains(server.handle_message("BEGIN session=1"), "OK")
var registry = server.registry
registry.set_txn(1, full_txn(MAX_TXN_WRITES))
server.registry = registry
val reply = server.handle_message("PUT session=1 tbl=users id=overflow name=x")
assert_contains(reply, "ERR")
assert_contains(reply, "code=limit")
# The bound also fences BATCH_PUT, which fans out through sys_write.
val batch = server.handle_message("BATCH_PUT session=1 tbl=users ids=b1,b2 name=x")
assert_contains(batch, "code=limit")
```

</details>

#### keeps the store and txn state intact after a bound refusal

- keeps the store and txn state intact after a bound refusal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the store and txn state intact after a bound refusal")
var server = make_server()
assert_contains(server.handle_message("OPEN as=alice credential=alice-secret"), "session=1")
assert_contains(server.handle_message("BEGIN session=1"), "OK")
var registry = server.registry
registry.set_txn(1, full_txn(MAX_TXN_WRITES))
server.registry = registry
server.handle_message("PUT session=1 tbl=users id=overflow name=x")
# Refusal must not have corrupted the session: ROLLBACK still works.
assert_contains(server.handle_message("ROLLBACK session=1"), "OK")
assert_contains(server.handle_message("BEGIN session=1"), "OK")
assert_contains(server.handle_message("PUT session=1 tbl=users id=u1 name=ada"), "OK")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-DBSERVER-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b34ab51b05f143f5468b8f42f2cbbd5961adc65b9ee687db8da1431c7e30a6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b34ab51b05f143f5468b8f42f2cbbd5961adc65b9ee687db8da1431c7e30a6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b34ab51b05f143f5468b8f42f2cbbd5961adc65b9ee687db8da1431c7e30a6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still serves a valid session, write and read (control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses OPEN once the open-session bound is reached' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/database/server/db_server_hardening_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows OPEN again after sessions are closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
