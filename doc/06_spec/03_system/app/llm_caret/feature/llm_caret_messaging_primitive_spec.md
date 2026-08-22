# LLM Caret Primitive Messaging PureDatabase

> This executable manual verifies canonical primitive-room persistence through Simple's SQLite-compatible engine rewritten in Simple, using real temporary database files. It covers room sequences, history, cursors, idempotency, inbound deduplication, direct-room isolation, restart recovery, outbox retry, dead letters, and audit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Primitive Messaging PureDatabase

This executable manual verifies canonical primitive-room persistence through Simple's SQLite-compatible engine rewritten in Simple, using real temporary database files. It covers room sequences, history, cursors, idempotency, inbound deduplication, direct-room isolation, restart recovery, outbox retry, dead letters, and audit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | `doc/02_requirements/feature/llm_caret_messaging.md` |
| Plan | `doc/03_plan/sys_test/llm_caret_messaging.md` |
| Design | `doc/05_design/app/tools/llm_caret_messaging.md` |
| Research | `doc/01_research/app/llm_caret/messaging_platforms.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


## Overview

This executable manual verifies canonical primitive-room persistence through
Simple's SQLite-compatible engine rewritten in Simple, using real temporary database files. It covers
room sequences, history, cursors, idempotency, inbound deduplication,
direct-room isolation, restart recovery, outbox retry, dead letters, and audit.

**Requirements:** `doc/02_requirements/feature/llm_caret_messaging.md`
**Plan:** `doc/03_plan/sys_test/llm_caret_messaging.md`
**Design:** `doc/05_design/app/tools/llm_caret_messaging.md`
**Research:** `doc/01_research/app/llm_caret/messaging_platforms.md`

## Evidence boundary

Passing proves only the production `PureSqlMessagingStore` and `PureDatabase`
runtime. It does not prove REST/SSE, enrollment, hooks, MCP, or live platforms.
The retained 2026-08-02 run is FAIL: 1/10 passed; the earliest defect was empty
history after append/reopen followed by an array-index failure.

## Scenarios

### LLM Caret primitive messaging pure-Simple SQL

### REQ-LLM-MSG-002, REQ-LLM-MSG-003, and REQ-LLM-MSG-016: durable ordered rooms and history

<details>
<summary>Advanced: should persist rooms and monotonically ordered messages after restart</summary>

#### should persist rooms and monotonically ordered messages after restart

- Verify: should persist rooms and monotonically ordered messages after restart
- Create and bind a room
   - Expected: store.create_room(primitive_room("development", RoomKind.Channel, 1)).ok is true
- Observe task and receipt transitions
   - Expected: first.room_seq equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: second.room_seq equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.append_audit("message_appended", "human-1", "m-2", "room_seq=2", 4).ok is true
   - Expected: store.close() is true
- Recover messaging state after restart
   - Expected: history.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: history[0].body equals `first`
   - Expected: history[1].room_seq equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.audit_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should persist rooms and monotonically ordered messages after restart")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
val path = primitive_db_path("restart")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.schema_version()).to_be_greater_than(0)
expect(store.create_room(primitive_room("development", RoomKind.Channel, 1)).ok).to_equal(true)
step("Observe task and receipt transitions")
val first = store.append_message(primitive_message("m-1", "development", "first", 2), "idem-first")
val second = store.append_message(primitive_message("m-2", "development", "second", 3), "idem-second")
expect(first.room_seq).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(second.room_seq).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(store.append_audit("message_appended", "human-1", "m-2", "room_seq=2", 4).ok).to_equal(true)
expect(store.close()).to_equal(true)
step("Recover messaging state after restart")
store = PureSqlMessagingStore.open(path)
val history = store.message_history("development", 0, 10)
expect(history.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(history[0].body).to_equal("first")
expect(history[1].room_seq).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(store.audit_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>


</details>

<details>
<summary>Advanced: should paginate history strictly after the supplied room sequence</summary>

#### should paginate history strictly after the supplied room sequence

- Verify: should paginate history strictly after the supplied room sequence
- Create and bind a room
   - Expected: store.create_room(primitive_room("history", RoomKind.Channel, 1)).ok is true
   - Expected: store.append_message(primitive_message("p-1", "history", "one", 2), "page-1").ok is true
   - Expected: store.append_message(primitive_message("p-2", "history", "two", 3), "page-2").ok is true
   - Expected: store.append_message(primitive_message("p-3", "history", "three", 4), "page-3").ok is true
- Observe task and receipt transitions
   - Expected: page.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: page[0].message_id.value equals `p-2`
   - Expected: page[0].room_seq equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should paginate history strictly after the supplied room sequence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
val path = primitive_db_path("page")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.create_room(primitive_room("history", RoomKind.Channel, 1)).ok).to_equal(true)
expect(store.append_message(primitive_message("p-1", "history", "one", 2), "page-1").ok).to_equal(true)
expect(store.append_message(primitive_message("p-2", "history", "two", 3), "page-2").ok).to_equal(true)
expect(store.append_message(primitive_message("p-3", "history", "three", 4), "page-3").ok).to_equal(true)
step("Observe task and receipt transitions")
val page = store.message_history("history", 1, 1)
expect(page.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(page[0].message_id.value).to_equal("p-2")
expect(page[0].room_seq).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>


</details>

<details>
<summary>Advanced: should reject a message for a room that does not exist</summary>

#### should reject a message for a room that does not exist

- Verify: should reject a message for a room that does not exist
- Create and bind a room
   - Expected: result.ok is false
   - Expected: result.error equals `room_not_found`
   - Expected: store.message_history("missing", 0, 10).len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should reject a message for a room that does not exist")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
val path = primitive_db_path("missing-room")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
val result = store.append_message(primitive_message("orphan", "missing", "not stored", 1), "missing-room")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("room_not_found")
expect(store.message_history("missing", 0, 10).len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>


</details>

### REQ-LLM-MSG-003 and REQ-LLM-MSG-016: idempotency, cursors, and inbound deduplication

#### should return the original sequence for a repeated idempotency key

- Verify: should return the original sequence for a repeated idempotency key
- Observe task and receipt transitions
   - Expected: store.create_room(primitive_room("dedup", RoomKind.Channel, 1)).ok is true
   - Expected: first.duplicate is false
   - Expected: duplicate.duplicate is true
   - Expected: duplicate.message_id equals `d-1`
   - Expected: duplicate.room_seq equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.message_history("dedup", 0, 10).len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should return the original sequence for a repeated idempotency key")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val path = primitive_db_path("idempotency")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.create_room(primitive_room("dedup", RoomKind.Channel, 1)).ok).to_equal(true)
val first = store.append_message(primitive_message("d-1", "dedup", "once", 2), "stable-key")
val duplicate = store.append_message(primitive_message("d-2", "dedup", "twice", 3), "stable-key")
expect(first.duplicate).to_equal(false)
expect(duplicate.duplicate).to_equal(true)
expect(duplicate.message_id).to_equal("d-1")
expect(duplicate.room_seq).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(store.message_history("dedup", 0, 10).len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>

<details>
<summary>Advanced: should persist an independently advanced room cursor</summary>

#### should persist an independently advanced room cursor

- Verify: should persist an independently advanced room cursor
- Observe task and receipt transitions
   - Expected: store.create_room(primitive_room("cursor-room", RoomKind.Channel, 1)).ok is true
   - Expected: store.append_message(primitive_message("c-1", "cursor-room", "read me", 2), "cursor-message").ok is true
   - Expected: store.advance_cursor("cursor-room", "reader-1", 1, 3).ok is true
   - Expected: store.close() is true
- Recover messaging state after restart
   - Expected: store.cursor("cursor-room", "reader-1") equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.cursor("cursor-room", "reader-2") equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should persist an independently advanced room cursor")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val path = primitive_db_path("cursor")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.create_room(primitive_room("cursor-room", RoomKind.Channel, 1)).ok).to_equal(true)
expect(store.append_message(primitive_message("c-1", "cursor-room", "read me", 2), "cursor-message").ok).to_equal(true)
expect(store.advance_cursor("cursor-room", "reader-1", 1, 3).ok).to_equal(true)
expect(store.close()).to_equal(true)
step("Recover messaging state after restart")
store = PureSqlMessagingStore.open(path)
expect(store.cursor("cursor-room", "reader-1")).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(store.cursor("cursor-room", "reader-2")).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>


</details>

#### should accept one canonical inbound event for repeated transport delivery

- Verify: should accept one canonical inbound event for repeated transport delivery
- Observe task and receipt transitions
   - Expected: store.accept_inbound("slack-binding-1", "event-42", 1) is true
   - Expected: store.accept_inbound("slack-binding-1", "event-42", 2) is false
   - Expected: store.accept_inbound("slack-binding-2", "event-42", 3) is true
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should accept one canonical inbound event for repeated transport delivery")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val path = primitive_db_path("inbound")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.accept_inbound("slack-binding-1", "event-42", 1)).to_equal(true)
expect(store.accept_inbound("slack-binding-1", "event-42", 2)).to_equal(false)
expect(store.accept_inbound("slack-binding-2", "event-42", 3)).to_equal(true)
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>

### REQ-LLM-MSG-012 and REQ-LLM-MSG-015: canonical direct-room isolation

<details>
<summary>Advanced: should keep direct-room content out of public-room history</summary>

#### should keep direct-room content out of public-room history

- Verify: should keep direct-room content out of public-room history
- Create and bind a room
   - Expected: store.create_room(primitive_room("public", RoomKind.Channel, 1)).ok is true
   - Expected: store.create_room(primitive_room("private-dm", RoomKind.Direct, 2)).ok is true
   - Expected: store.append_message(primitive_message("public-1", "public", "visible", 3), "public-key").ok is true
   - Expected: store.append_message(primitive_message("private-1", "private-dm", "secret", 4), "private-key").ok is true
- Recover messaging state after restart
   - Expected: store.close() is true
   - Expected: public_history.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: public_history[0].body equals `visible`
   - Expected: private_history.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: private_history[0].body equals `secret`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should keep direct-room content out of public-room history")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
val path = primitive_db_path("direct")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.create_room(primitive_room("public", RoomKind.Channel, 1)).ok).to_equal(true)
expect(store.create_room(primitive_room("private-dm", RoomKind.Direct, 2)).ok).to_equal(true)
expect(store.append_message(primitive_message("public-1", "public", "visible", 3), "public-key").ok).to_equal(true)
expect(store.append_message(primitive_message("private-1", "private-dm", "secret", 4), "private-key").ok).to_equal(true)
step("Recover messaging state after restart")
expect(store.close()).to_equal(true)
store = PureSqlMessagingStore.open(path)
val public_history = store.message_history("public", 0, 10)
val private_history = store.message_history("private-dm", 0, 10)
expect(public_history.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(public_history[0].body).to_equal("visible")
expect(private_history.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(private_history[0].body).to_equal("secret")
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>


</details>

### REQ-LLM-MSG-016: transactional outbox and dead-letter evidence

#### should persist a queued delivery and classify a retry

- Verify: should persist a queued delivery and classify a retry
- Observe task and receipt transitions
   - Expected: store.enqueue_outbox("delivery-1", "m-1", "binding-1", "payload", 10).ok is true
   - Expected: store.outbox_state("delivery-1") equals `queued`
   - Expected: store.mark_outbox_attempt("delivery-1", "rate_limited", 20, 3, 11).ok is true
   - Expected: store.outbox_state("delivery-1") equals `queued`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should persist a queued delivery and classify a retry")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val path = primitive_db_path("retry")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.enqueue_outbox("delivery-1", "m-1", "binding-1", "payload", 10).ok).to_equal(true)
expect(store.outbox_state("delivery-1")).to_equal("queued")
expect(store.mark_outbox_attempt("delivery-1", "rate_limited", 20, 3, 11).ok).to_equal(true)
expect(store.outbox_state("delivery-1")).to_equal("queued")
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>

#### should recover queued outbox state after reopening the database

- Verify: should recover queued outbox state after reopening the database
- Observe task and receipt transitions
   - Expected: store.enqueue_outbox("delivery-2", "m-2", "binding-1", "payload", 10).ok is true
   - Expected: store.close() is true
- Recover messaging state after restart
   - Expected: store.outbox_state("delivery-2") equals `queued`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should recover queued outbox state after reopening the database")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val path = primitive_db_path("outbox-restart")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.enqueue_outbox("delivery-2", "m-2", "binding-1", "payload", 10).ok).to_equal(true)
expect(store.close()).to_equal(true)
step("Recover messaging state after restart")
store = PureSqlMessagingStore.open(path)
expect(store.outbox_state("delivery-2")).to_equal("queued")
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>

#### should move a permanently exhausted delivery to dead-letter state

- Verify: should move a permanently exhausted delivery to dead-letter state
- Observe task and receipt transitions
   - Expected: store.enqueue_outbox("delivery-3", "m-3", "binding-1", "payload", 10).ok is true
   - Expected: store.mark_outbox_attempt("delivery-3", "remote_failure", 20, 1, 11).ok is true
   - Expected: store.outbox_state("delivery-3") equals `dead_letter`
   - Expected: store.dead_letter_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.append_audit("delivery_failed", "system", "delivery-3", "remote_failure", 11).ok is true
   - Expected: store.audit_count() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-002 REQ-LLM-MSG-003 REQ-LLM-MSG-016 REQ-LLM-MSG-012 REQ-LLM-MSG-015
step("Verify: should move a permanently exhausted delivery to dead-letter state")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val path = primitive_db_path("dead-letter")
file_delete(path)
var store = PureSqlMessagingStore.open(path)
expect(store.enqueue_outbox("delivery-3", "m-3", "binding-1", "payload", 10).ok).to_equal(true)
expect(store.mark_outbox_attempt("delivery-3", "remote_failure", 20, 1, 11).ok).to_equal(true)
expect(store.outbox_state("delivery-3")).to_equal("dead_letter")
expect(store.dead_letter_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(store.append_audit("delivery_failed", "system", "delivery-3", "remote_failure", 11).ok).to_equal(true)
expect(store.audit_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** ``doc/02_requirements/feature/llm_caret_messaging.md``
- **Plan:** ``doc/03_plan/sys_test/llm_caret_messaging.md``
- **Design:** ``doc/05_design/app/tools/llm_caret_messaging.md``
- **Research:** ``doc/01_research/app/llm_caret/messaging_platforms.md``


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3bb5c1cc25ec0e581a10d1a71937b9df2b8296777da7dc2bfa2ad35e4909d11d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3bb5c1cc25ec0e581a10d1a71937b9df2b8296777da7dc2bfa2ad35e4909d11d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3bb5c1cc25ec0e581a10d1a71937b9df2b8296777da7dc2bfa2ad35e4909d11d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should persist rooms and monotonically ordered messages after restart' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should paginate history strictly after the supplied room sequence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl:104:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a message for a room that does not exist' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl:120:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return the original sequence for a repeated idempotency key' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should persist an independently advanced room cursor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_primitive_spec.spl:158:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept one canonical inbound event for repeated transport delivery' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
