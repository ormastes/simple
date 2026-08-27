# pure_sql_store_spec

> Pure-Simple SQL persistence preserves canonical messaging state and truth.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pure_sql_store_spec

Pure-Simple SQL persistence preserves canonical messaging state and truth.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure-Simple SQL persistence preserves canonical messaging state and truth.

## Scenarios

### LLM Caret pure-Simple SQL store

<details>
<summary>Advanced: allocates monotonic room sequences and deduplicates canonical writes</summary>

#### allocates monotonic room sequences and deduplicates canonical writes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allocates monotonic room sequences and deduplicates canonical writes
- Open the embedded database and create the complete primitive schema
   - Expected: store.ready() is true
   - Expected: store.table_ready("context_manifests") is true
   - Expected: store.table_ready("dead_letters") is true
   - Expected: store.table_ready("artifacts") is true
   - Expected: store.table_ready("mcp_idempotency") is true
   - Expected: store.table_ready("transport_bindings") is true
   - Expected: store.table_ready("external_refs") is true
   - Expected: store.table_ready("canonical_events") is true
   - Expected: store.table_ready("workspaces") is true
   - Expected: store.table_ready("identities") is true
   - Expected: store.table_ready("task_events") is true
   - Expected: store.create_room(room("r1", RoomKind.Channel)).ok is true
- Append messages with server-owned monotonic room sequence
   - Expected: first.room_seq equals `1`
   - Expected: second.room_seq equals `2`
- Replay the same idempotency key without creating another message
   - Expected: replay.duplicate is true
   - Expected: replay.message_id equals `m1`
   - Expected: store.message_count() equals `2`
   - Expected: store.canonical_event_count() equals `3`
- Read ordered history and advance a monotonic local cursor
   - Expected: history.len() equals `2`
   - Expected: history[0].body equals `first 'quoted' message`
   - Expected: history[1].room_seq equals `2`
   - Expected: store.advance_cursor("r1", "human-1", 2, 30).ok is true
   - Expected: store.advance_cursor("r1", "human-1", 1, 31).ok is true
   - Expected: store.cursor("r1", "human-1") equals `2`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allocates monotonic room sequences and deduplicates canonical writes")
step("Open the embedded database and create the complete primitive schema")
val path = "/tmp/llm_caret_store_sequence_" + getpid().to_text() + ".db"
file_delete(path)
val store = PureSqlMessagingStore.open(path)
expect(store.ready()).to_equal(true)
expect(store.table_ready("context_manifests")).to_equal(true)
expect(store.table_ready("dead_letters")).to_equal(true)
expect(store.table_ready("artifacts")).to_equal(true)
expect(store.table_ready("mcp_idempotency")).to_equal(true)
expect(store.table_ready("transport_bindings")).to_equal(true)
expect(store.table_ready("external_refs")).to_equal(true)
expect(store.table_ready("canonical_events")).to_equal(true)
expect(store.table_ready("workspaces")).to_equal(true)
expect(store.table_ready("identities")).to_equal(true)
expect(store.table_ready("task_events")).to_equal(true)
expect(store.create_room(room("r1", RoomKind.Channel)).ok).to_equal(true)

step("Append messages with server-owned monotonic room sequence")
val first = store.append_message(message("m1", "r1", "first 'quoted' message"), "request-1")
val second = store.append_message(message("m2", "r1", "second"), "request-2")
expect(first.room_seq).to_equal(1)
expect(second.room_seq).to_equal(2)

step("Replay the same idempotency key without creating another message")
val replay = store.append_message(message("m-replay", "r1", "ignored"), "request-1")
expect(replay.duplicate).to_equal(true)
expect(replay.message_id).to_equal("m1")
expect(store.message_count()).to_equal(2)
expect(store.canonical_event_count()).to_equal(3)

step("Read ordered history and advance a monotonic local cursor")
val history = store.message_history("r1", 0, 10)
expect(history.len()).to_equal(2)
expect(history[0].body).to_equal("first 'quoted' message")
expect(history[1].room_seq).to_equal(2)
expect(store.advance_cursor("r1", "human-1", 2, 30).ok).to_equal(true)
expect(store.advance_cursor("r1", "human-1", 1, 31).ok).to_equal(true)
expect(store.cursor("r1", "human-1")).to_equal(2)
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>


</details>

#### persists artifacts, context manifests, and MCP idempotency evidence

- persists artifacts, context manifests, and MCP idempotency evidence
   - Expected: store.put_artifact(artifact).ok is true
   - Expected: store.artifacts().len() equals `1`
   - Expected: store.artifacts()[0].value equals `report`
   - Expected: store.context_manifest_count() equals `1`
   - Expected: store.put_mcp_idempotency("stable-key-1", "artifact-1", "artifact_published", 12).ok is true
   - Expected: store.mcp_idempotency("stable-key-1").resource_id equals `artifact-1`
   - Expected: store.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("persists artifacts, context manifests, and MCP idempotency evidence")
val path = "/tmp/llm_caret_store_artifact_" + getpid().to_text() + ".db"
file_delete(path)
val store = PureSqlMessagingStore.open(path)
val artifact = StoredArtifact(artifact_id: "artifact-1", task_id: "task-1", room_id: "room-1",
    media_type: "text/plain", value: "report", published_by: "agent-1", created_at: 10)
expect(store.put_artifact(artifact).ok).to_equal(true)
expect(store.artifacts().len()).to_equal(1)
expect(store.artifacts()[0].value).to_equal("report")
expect(store.put_context_manifest("context-1", "task-1", ["message-1"], ["agent-1"],
    "source-hash", "summary-v1", "redaction-v1", 12, 11).ok).to_equal(true)
expect(store.context_manifest_count()).to_equal(1)
expect(store.put_mcp_idempotency("stable-key-1", "artifact-1", "artifact_published", 12).ok).to_equal(true)
expect(store.mcp_idempotency("stable-key-1").resource_id).to_equal("artifact-1")
expect(store.close()).to_equal(true)
file_delete(path)
```

</details>

<details>
<summary>Advanced: recovers rooms, history, cursors, deduplication, and delivery state after reopen</summary>

#### recovers rooms, history, cursors, deduplication, and delivery state after reopen

- recovers rooms, history, cursors, deduplication, and delivery state after reopen
- Create durable canonical state and close the first process connection
   - Expected: first_store.create_room(room("direct-1", RoomKind.Direct)).ok is true
   - Expected: first_store.append_message(message("dm-1", "direct-1", "private"), "dm-request-1").room_seq equals `1`
   - Expected: first_store.advance_cursor("direct-1", "human-1", 1, 40).ok is true
   - Expected: first_store.accept_inbound("slack-1", "event-1", 41) is true
   - Expected: first_store.accept_inbound("slack-1", "event-1", 42) is false
   - Expected: first_store.enqueue_outbox("delivery-1", "dm-1", "slack-1", "payload", 43).ok is true
   - Expected: first_store.mark_outbox_attempt("delivery-1", "rate_limited", 50, 2, 44).ok is true
   - Expected: first_store.outbox_state("delivery-1") equals `queued`
   - Expected: first_store.enqueue_outbox("delivery-2", "dm-1", "slack-1", "payload-2", 45).ok is true
   - Expected: first_store.mark_outbox_delivered("delivery-2", 46).ok is true
   - Expected: first_store.outbox_state("delivery-2") equals `delivered`
   - Expected: first_store.enqueue_transport_request(transport_request, 47).ok is true
   - Expected: first_store.close() is true
- Reopen the same embedded database and recover projections and retry state
   - Expected: recovered.schema_version() equals `1`
   - Expected: recovered.room("direct-1").kind equals `RoomKind.Direct`
   - Expected: recovered.message_history("direct-1", 0, 10)[0].body equals `private`
   - Expected: recovered.cursor("direct-1", "human-1") equals `1`
   - Expected: recovered.accept_inbound("slack-1", "event-1", 60) is false
   - Expected: recovered.outbox_state("delivery-2") equals `delivered`
   - Expected: queued_requests.len() equals `1`
   - Expected: queued_requests[0].credential_ref equals `secret://slack/development`
   - Expected: queued_requests[0].headers.join(" | ") does not contain `Authorization:`
   - Expected: recovered.canonical_event_count() equals `3`
   - Expected: recovered.canonical_events()[0].event_kind equals `room_created`
   - Expected: recovered.transport_binding("slack-1").external_room_id equals `D123`
   - Expected: recovered.transport_binding("slack-1").last_outbound_cursor equals `ts-1`
   - Expected: recovered.external_ref("slack-1", "dm-1").external_message_id equals `171.1`
   - Expected: recovered.external_ref("slack-1", "dm-1").external_thread_id equals `170.1`
   - Expected: recovered.mark_outbox_attempt("delivery-1", "permanent", 0, 2, 61).ok is true
   - Expected: recovered.outbox_state("delivery-1") equals `dead_letter`
   - Expected: recovered.dead_letter_count() equals `1`
   - Expected: recovered.append_audit("delivery_failed", "system", "delivery-1", "permanent", 61).ok is true
   - Expected: recovered.audit_count() equals `1`
   - Expected: recovered.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recovers rooms, history, cursors, deduplication, and delivery state after reopen")
step("Create durable canonical state and close the first process connection")
val path = "/tmp/llm_caret_store_restart_" + getpid().to_text() + ".db"
file_delete(path)
val first_store = PureSqlMessagingStore.open(path)
expect(first_store.create_room(room("direct-1", RoomKind.Direct)).ok).to_equal(true)
expect(first_store.append_message(message("dm-1", "direct-1", "private"), "dm-request-1").room_seq).to_equal(1)
expect(first_store.advance_cursor("direct-1", "human-1", 1, 40).ok).to_equal(true)
expect(first_store.accept_inbound("slack-1", "event-1", 41)).to_equal(true)
expect(first_store.accept_inbound("slack-1", "event-1", 42)).to_equal(false)
expect(first_store.enqueue_outbox("delivery-1", "dm-1", "slack-1", "payload", 43).ok).to_equal(true)
expect(first_store.put_transport_binding(StoredTransportBinding(binding_id: "slack-1",
    canonical_room_id: "direct-1", transport: "slack", external_room_id: "D123",
    mirror_policy: "full", capabilities_version: "slack-v1",
    last_inbound_cursor: "event-1", last_outbound_cursor: "ts-1")).ok).to_equal(true)
expect(first_store.put_external_ref(StoredExternalRef(ref_id: "slack-1:dm-1",
    binding_id: "slack-1", canonical_message_id: "dm-1", external_message_id: "171.1",
    external_thread_id: "170.1", created_at: 44)).ok).to_equal(true)
expect(first_store.mark_outbox_attempt("delivery-1", "rate_limited", 50, 2, 44).ok).to_equal(true)
expect(first_store.outbox_state("delivery-1")).to_equal("queued")
expect(first_store.enqueue_outbox("delivery-2", "dm-1", "slack-1", "payload-2", 45).ok).to_equal(true)
expect(first_store.mark_outbox_delivered("delivery-2", 46).ok).to_equal(true)
expect(first_store.outbox_state("delivery-2")).to_equal("delivered")
val transport_request = StoredTransportRequest(delivery_id: "delivery-3", message_id: "dm-1",
    binding_id: "slack-1", method: "POST", url_template: "https://slack.com/api/chat.postMessage",
    headers: ["Content-Type: application/json"], body: "{}",
    credential_ref: "secret://slack/development", credential_mode: "bearer",
    idempotency_key: "stable-delivery-3")
expect(first_store.enqueue_transport_request(transport_request, 47).ok).to_equal(true)
expect(first_store.close()).to_equal(true)

step("Reopen the same embedded database and recover projections and retry state")
val recovered = PureSqlMessagingStore.open(path)
expect(recovered.schema_version()).to_equal(1)
expect(recovered.room("direct-1").kind).to_equal(RoomKind.Direct)
expect(recovered.message_history("direct-1", 0, 10)[0].body).to_equal("private")
expect(recovered.cursor("direct-1", "human-1")).to_equal(1)
expect(recovered.accept_inbound("slack-1", "event-1", 60)).to_equal(false)
expect(recovered.outbox_state("delivery-2")).to_equal("delivered")
val queued_requests = recovered.queued_transport_requests(100, 10)
expect(queued_requests.len()).to_equal(1)
expect(queued_requests[0].credential_ref).to_equal("secret://slack/development")
expect(queued_requests[0].headers.join(" | ").contains("Authorization:")).to_equal(false)
expect(recovered.canonical_event_count()).to_equal(3)
expect(recovered.canonical_events()[0].event_kind).to_equal("room_created")
expect(recovered.transport_binding("slack-1").external_room_id).to_equal("D123")
expect(recovered.transport_binding("slack-1").last_outbound_cursor).to_equal("ts-1")
expect(recovered.external_ref("slack-1", "dm-1").external_message_id).to_equal("171.1")
expect(recovered.external_ref("slack-1", "dm-1").external_thread_id).to_equal("170.1")
expect(recovered.mark_outbox_attempt("delivery-1", "permanent", 0, 2, 61).ok).to_equal(true)
expect(recovered.outbox_state("delivery-1")).to_equal("dead_letter")
expect(recovered.dead_letter_count()).to_equal(1)
expect(recovered.append_audit("delivery_failed", "system", "delivery-1", "permanent", 61).ok).to_equal(true)
expect(recovered.audit_count()).to_equal(1)
expect(recovered.close()).to_equal(true)
file_delete(path)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-002`
- `REQ-LLM-MSG-003`
- `REQ-LLM-MSG-008`
- `REQ-LLM-MSG-012`
- `REQ-LLM-MSG-016`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a122e7a8fd1d44321505be47dd4ee71d0b8a6b5468f6a30196b16730c228f2c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a122e7a8fd1d44321505be47dd4ee71d0b8a6b5468f6a30196b16730c228f2c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a122e7a8fd1d44321505be47dd4ee71d0b8a6b5468f6a30196b16730c228f2c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/pure_sql_store_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/pure_sql_store_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/pure_sql_store_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates monotonic room sequences and deduplicates canonical writes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists artifacts, context manifests, and MCP idempotency evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recovers rooms, history, cursors, deduplication, and delivery state after reopen' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
