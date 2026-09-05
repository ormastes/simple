# LLM Caret Primitive HTTP Application

> Executable request-dispatch evidence for authorization, idempotency, rooms,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Primitive HTTP Application

Executable request-dispatch evidence for authorization, idempotency, rooms,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_http_application_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Executable request-dispatch evidence for authorization, idempotency, rooms,
messages, history, cursors, SSE, direct-room ACL, and restart recovery.

## Scenarios

### LLM Caret primitive HTTP application

<details>
<summary>Advanced: creates a room, sends once, reads history, advances a cursor, and streams SSE</summary>

#### creates a room, sends once, reads history, advances a cursor, and streams SSE

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a room, sends once, reads history, advances a cursor, and streams SSE
- Create and bind a room
   - Expected: created.status equals `202`
   - Expected: bound.status equals `201`
- Route a message to an agent
   - Expected: sent.status equals `202`
   - Expected: task.status equals `200`
- Observe task and receipt transitions
   - Expected: events.content_type equals `text/event-stream`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a room, sends once, reads history, advances a cursor, and streams SSE")
step("Create and bind a room")
var app = PrimitiveMessagingApplication.memory()
val owner = http_principal("owner-http", ["room:manage", "room:write", "room:read",
    "agent:control", "profile:read"])
val created = app.handle(http_request("POST", "/v1/rooms",
    "{\"room_id\":\"http-room\",\"kind\":\"channel\",\"name\":\"HTTP Room\",\"topic\":\"test\",\"visibility\":\"public\",\"mode\":\"room\"}",
    "create-http-room", owner, 1))
expect(created.status).to_equal(202)
expect(app.handle(http_request("POST", "/v1/agents",
    "{\"agent_id\":\"http-agent\",\"display_name\":\"builder-claude-01\",\"provider\":\"claude\",\"role_summary\":\"implementation\"}",
    "create-http-agent", owner, 2)).status).to_equal(202)
val bound = app.handle(http_request("POST", "/v1/agent-bindings",
    "{\"binding_id\":\"http-agent-binding\",\"agent_id\":\"http-agent\",\"provider\":\"claude\",\"room_id\":\"http-room\",\"handler\":\"main\",\"session_policy\":\"persistent_per_room\",\"trigger_policy\":\"room\",\"update_policy\":\"milestones\",\"context_policy\":\"bounded\"}",
    "bind-http-agent", owner, 3))
expect(bound.status).to_equal(201)
step("Route a message to an agent")
val sent = app.handle(http_request("POST", "/v1/rooms/http-room/messages",
    "{\"message_id\":\"http-message-1\",\"body\":\"hello over HTTP\",\"correlation_id\":\"http-correlation\",\"main_agent_id\":\"http-agent\"}",
    "send-http-message", owner, 4))
expect(sent.status).to_equal(202)
expect(sent.body).to_contain("\"room_seq\":1")
expect(sent.body).to_contain("\"routed\":true")
expect(sent.body).to_contain("\"task_id\":\"task-http-message-1\"")
val task = app.handle(http_request("GET", "/v1/tasks/task-http-message-1", "", "",
    owner, 5))
expect(task.status).to_equal(200)
val duplicate = app.handle(http_request("POST", "/v1/rooms/http-room/messages",
    "{\"message_id\":\"different-id\",\"body\":\"duplicate\"}",
    "send-http-message", owner, 6))
expect(duplicate.body).to_contain("\"duplicate\":true")
step("Observe task and receipt transitions")
val history = app.handle(http_request("GET", "/v1/rooms/http-room/messages?after_seq=0&limit=10",
    "", "", owner, 7))
expect(history.body).to_contain("hello over HTTP")
val cursor = app.handle(http_request("PUT", "/v1/rooms/http-room/cursor",
    "{\"room_seq\":1}", "cursor-http-0001", owner, 8))
expect(cursor.body).to_contain("local_cursor")
val tagged = app.handle(http_request("GET", "/v1/rooms/http-room/messages?after_seq=0&limit=10",
    "", "", owner, 9))
expect(tagged.body).to_contain("[read:local]")
val events = app.handle(http_request("GET", "/v1/rooms/http-room/events?after_seq=0",
    "", "", owner, 10))
expect(events.content_type).to_equal("text/event-stream")
expect(events.body).to_contain("event: message")
```

</details>


</details>

<details>
<summary>Advanced: persists direct-room membership and denies an outsider after restart</summary>

#### persists direct-room membership and denies an outsider after restart

- persists direct-room membership and denies an outsider after restart
- Create and bind a room
   - Expected: app.close() is true
- Recover messaging state after restart
   - Expected: app.handle(http_request("GET", "/v1/rooms/private-http", "", "", member, 2)).status equals `200`
   - Expected: app.handle(http_request("GET", "/v1/rooms/private-http", "", "", outsider, 2)).status equals `403`
   - Expected: app.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("persists direct-room membership and denies an outsider after restart")
step("Create and bind a room")
val path = "/tmp/llm_caret_http_restart_" + getpid().to_text() + ".db"
file_delete(path)
var app = PrimitiveMessagingApplication.open(path)
val owner = http_principal("owner-http", ["dm:write", "room:write", "room:read"])
expect(app.handle(http_request("POST", "/v1/direct-rooms",
    "{\"room_id\":\"private-http\",\"target_identity_id\":\"agent-http\"}",
    "create-private-http", owner, 1)).status).to_equal(202)
expect(app.close()).to_equal(true)
step("Recover messaging state after restart")
app = PrimitiveMessagingApplication.open(path)
val member = http_principal("agent-http", ["room:read"])
val outsider = http_principal("outsider-http", ["room:read"])
expect(app.handle(http_request("GET", "/v1/rooms/private-http", "", "", member, 2)).status).to_equal(200)
expect(app.handle(http_request("GET", "/v1/rooms/private-http", "", "", outsider, 2)).status).to_equal(403)
expect(app.close()).to_equal(true)
file_delete(path)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e1f809596e20afba1cad1a54aa5dbd4f0ba2add66f0d5c9592200021a23fa791`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1f809596e20afba1cad1a54aa5dbd4f0ba2add66f0d5c9592200021a23fa791`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1f809596e20afba1cad1a54aa5dbd4f0ba2add66f0d5c9592200021a23fa791`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_http_application_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_http_application_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_http_application_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_http_application_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_messaging_http_application_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_messaging_http_application_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a room, sends once, reads history, advances a cursor, and streams SSE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_messaging_http_application_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'persists direct-room membership and denies an outsider after restart' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
