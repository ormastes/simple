# mcp_server_spec

> The dedicated MCP core exposes all canonical chat operations safely.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_server_spec

The dedicated MCP core exposes all canonical chat operations safely.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/mcp_server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The dedicated MCP core exposes all canonical chat operations safely.

## Scenarios

### LLM Caret messaging MCP server

#### joins, leaves, sends, reads, and records truthful local read evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- joins, leaves, sends, reads, and records truthful local read evidence
- Join and send through scoped mutation calls with stable keys
   - Expected: server.dispatch(request(ChatTool.Join, ["room:write"], "join-key-001")).ok is true
   - Expected: sent.ok is true
   - Expected: sent.evidence equals `accepted`
- Read only a bounded canonical page and advance a local cursor
   - Expected: read.messages.len() equals `1`
   - Expected: marked.evidence equals `local_cursor`
   - Expected: server.dispatch(request(ChatTool.Leave, ["room:write"], "leave-key-001")).ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("joins, leaves, sends, reads, and records truthful local read evidence")
val server = server_with_room()
step("Join and send through scoped mutation calls with stable keys")
expect(server.dispatch(request(ChatTool.Join, ["room:write"], "join-key-001")).ok).to_equal(true)
val sent = server.dispatch(request(ChatTool.Send, ["room:write"], "send-key-001"))
expect(sent.ok).to_equal(true)
expect(sent.evidence).to_equal("accepted")

step("Read only a bounded canonical page and advance a local cursor")
val read = server.dispatch(request(ChatTool.Read, ["room:read"], ""))
expect(read.messages.len()).to_equal(1)
var marked_request = request(ChatTool.MarkRead, ["room:read"], "cursor-key-001")
marked_request.after_seq = 1
val marked = server.dispatch(marked_request)
expect(marked.evidence).to_equal("local_cursor")
expect(server.dispatch(request(ChatTool.Leave, ["room:write"], "leave-key-001")).ok).to_equal(true)
server.close()
```

</details>

#### queries profiles and builds bounded context without transcript reconstruction

- queries profiles and builds bounded context without transcript reconstruction
- Resolve a canonical profile by agent identity
   - Expected: who.profiles.len() equals `1`
   - Expected: who.profiles[0].display_name equals `builder-claude-01`
- Cap injection context even when a caller requests an excessive page
   - Expected: context.ok is true
   - Expected: context.evidence equals `bounded_context_manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("queries profiles and builds bounded context without transcript reconstruction")
val server = server_with_room()
server.dispatch(request(ChatTool.Send, ["room:write"], "send-key-ctx1"))

step("Resolve a canonical profile by agent identity")
val who = server.dispatch(request(ChatTool.Who, ["profile:read"], ""))
expect(who.profiles.len()).to_equal(1)
expect(who.profiles[0].display_name).to_equal("builder-claude-01")

step("Cap injection context even when a caller requests an excessive page")
var context_request = request(ChatTool.GetContext, ["room:read"], "")
context_request.limit = 5000
val context = server.dispatch(context_request)
expect(context.ok).to_equal(true)
expect(context.evidence).to_equal("bounded_context_manifest")
expect(context.messages.len()).to_be_less_than(33)
server.close()
```

</details>

<details>
<summary>Advanced: opens private rooms and protects notify-all with scope and origin policy</summary>

#### opens private rooms and protects notify-all with scope and origin policy

- opens private rooms and protects notify-all with scope and origin policy
- Create a canonical primitive direct room when requested
   - Expected: server.dispatch(direct).evidence equals `primitive_direct_room`
- Reject broadcast without room management and reject agent progress loops
   - Expected: server.dispatch(request(ChatTool.NotifyAll, ["room:write"], "notify-key-1")).status equals `403`
   - Expected: server.dispatch(update).error equals `agent_update_cannot_notify_all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("opens private rooms and protects notify-all with scope and origin policy")
val server = server_with_room()
step("Create a canonical primitive direct room when requested")
var direct = request(ChatTool.OpenPrivate, ["dm:write"], "direct-key-01")
direct.room_id = "direct-1"
expect(server.dispatch(direct).evidence).to_equal("primitive_direct_room")

step("Reject broadcast without room management and reject agent progress loops")
expect(server.dispatch(request(ChatTool.NotifyAll, ["room:write"], "notify-key-1")).status).to_equal(403)
var update = request(ChatTool.NotifyAll, ["room:write", "room:manage"], "notify-key-2")
update.origin = MessageOrigin.AgentUpdate
expect(server.dispatch(update).error).to_equal("agent_update_cannot_notify_all")
server.close()
```

</details>


</details>

#### assigns tasks, publishes artifacts, and transitions significant state

- assigns tasks, publishes artifacts, and transitions significant state
- Assign a stateful task independently from its origin message
   - Expected: assigned.ok is true
   - Expected: assigned.tasks[0].state equals `TaskState.Queued`
- Publish a durable artifact and update the task state
   - Expected: artifact.artifacts[0].artifact_id equals `artifact-1`
   - Expected: updated.tasks[0].state equals `TaskState.Running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("assigns tasks, publishes artifacts, and transitions significant state")
val server = server_with_room()
step("Assign a stateful task independently from its origin message")
val assigned = server.dispatch(request(ChatTool.Assign, ["agent:control"], "assign-key-01"))
expect(assigned.ok).to_equal(true)
expect(assigned.tasks[0].state).to_equal(TaskState.Queued)

step("Publish a durable artifact and update the task state")
val artifact = server.dispatch(request(ChatTool.PublishArtifact, ["agent:control"], "artifact-key1"))
expect(artifact.artifacts[0].artifact_id).to_equal("artifact-1")
val updated = server.dispatch(request(ChatTool.TaskUpdate, ["agent:control"], "update-key-01"))
expect(updated.tasks[0].state).to_equal(TaskState.Running)
server.close()
```

</details>

#### fails closed on scopes, unstable mutation keys, and duplicate calls

- fails closed on scopes, unstable mutation keys, and duplicate calls
- Require the exact tool scope and a stable bounded idempotency key
   - Expected: server.dispatch(request(ChatTool.Send, ["room:read"], "send-key-auth")).error equals `scope_required:room:write`
   - Expected: server.dispatch(request(ChatTool.Send, ["room:write"], "tiny")).error equals `stable_idempotency_key_required`
- Return a truthful replay result without applying a mutation twice
   - Expected: server.dispatch(request(ChatTool.Join, ["room:write"], "replay-key-01")).duplicate is false
   - Expected: server.dispatch(request(ChatTool.Join, ["room:write"], "replay-key-01")).duplicate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed on scopes, unstable mutation keys, and duplicate calls")
val server = server_with_room()
step("Require the exact tool scope and a stable bounded idempotency key")
expect(server.dispatch(request(ChatTool.Send, ["room:read"], "send-key-auth")).error).to_equal("scope_required:room:write")
expect(server.dispatch(request(ChatTool.Send, ["room:write"], "tiny")).error).to_equal("stable_idempotency_key_required")

step("Return a truthful replay result without applying a mutation twice")
expect(server.dispatch(request(ChatTool.Join, ["room:write"], "replay-key-01")).duplicate).to_equal(false)
expect(server.dispatch(request(ChatTool.Join, ["room:write"], "replay-key-01")).duplicate).to_equal(true)
server.close()
```

</details>

#### recovers MCP memberships, profiles, tasks, artifacts, manifests, and idempotency after restart

- recovers MCP memberships, profiles, tasks, artifacts, manifests, and idempotency after restart
   - Expected: server.register_room(created.room, created.memberships) is true
   - Expected: server.dispatch(request(ChatTool.Assign, ["agent:control"], "durable-assign-1")).ok is true
   - Expected: server.dispatch(request(ChatTool.PublishArtifact, ["agent:control"], "durable-artifact-1")).ok is true
   - Expected: server.dispatch(request(ChatTool.Send, ["room:write"], "durable-send-01")).ok is true
   - Expected: server.dispatch(request(ChatTool.GetContext, ["room:read"], "")).ok is true
   - Expected: server.store.context_manifest_count() equals `1`
   - Expected: server.close() is true
- Reopen the same PureDatabase file and recover every MCP projection
   - Expected: server.dispatch(request(ChatTool.Who, ["profile:read"], "")).profiles.len() equals `1`
   - Expected: server.tasks.len() equals `1`
   - Expected: server.artifacts.len() equals `1`
   - Expected: server.store.context_manifest_count() equals `1`
   - Expected: replay.duplicate is true
   - Expected: replay.resource_id equals `task-1`
   - Expected: server.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("recovers MCP memberships, profiles, tasks, artifacts, manifests, and idempotency after restart")
val path = "/tmp/llm_caret_mcp_restart_" + getpid().to_text() + ".db"
file_delete(path)
var server = MessagingMcpServer.open(path)
val created = create_room("room-1", "ws-1", RoomKind.Channel, "development", "", "public",
    "mention", "milestones", "bounded", "human-1", 1)
expect(server.register_room(created.room, created.memberships)).to_equal(true)
server.register_profile(AgentProfile(agent_id: messaging_id("agent", "builder-1"),
    display_name: "builder-claude-01", aliases: ["builder"], provider: "claude",
    role_summary: "implementation", capabilities: ["code"], current_task_id: "",
    status: AgentStatus.Idle, owner_identity_id: "human-1", room_ids: ["room-1"],
    last_activity_at: 1))
expect(server.dispatch(request(ChatTool.Assign, ["agent:control"], "durable-assign-1")).ok).to_equal(true)
expect(server.dispatch(request(ChatTool.PublishArtifact, ["agent:control"], "durable-artifact-1")).ok).to_equal(true)
expect(server.dispatch(request(ChatTool.Send, ["room:write"], "durable-send-01")).ok).to_equal(true)
expect(server.dispatch(request(ChatTool.GetContext, ["room:read"], "")).ok).to_equal(true)
expect(server.store.context_manifest_count()).to_equal(1)
expect(server.close()).to_equal(true)

step("Reopen the same PureDatabase file and recover every MCP projection")
server = MessagingMcpServer.open(path)
expect(server.dispatch(request(ChatTool.Who, ["profile:read"], "")).profiles.len()).to_equal(1)
expect(server.tasks.len()).to_equal(1)
expect(server.artifacts.len()).to_equal(1)
expect(server.memberships.len()).to_be_greater_than(0)
expect(server.store.context_manifest_count()).to_equal(1)
val replay = server.dispatch(request(ChatTool.Assign, ["agent:control"], "durable-assign-1"))
expect(replay.duplicate).to_equal(true)
expect(replay.resource_id).to_equal("task-1")
expect(server.close()).to_equal(true)
file_delete(path)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-003`
- `REQ-LLM-MSG-007`
- `REQ-LLM-MSG-009`
- `REQ-LLM-MSG-011`
- `REQ-LLM-MSG-014`
- `REQ-LLM-MSG-015`
- `REQ-LLM-MSG-016`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2d8126edbb998b474411031724627046601c1c4ea2f4e66aa2eff3fa7edebc7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2d8126edbb998b474411031724627046601c1c4ea2f4e66aa2eff3fa7edebc7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2d8126edbb998b474411031724627046601c1c4ea2f4e66aa2eff3fa7edebc7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/mcp_server_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/mcp_server_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/mcp_server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/mcp_server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/mcp_server_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/mcp_server_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 8 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/mcp_server_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins, leaves, sends, reads, and records truthful local read evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/mcp_server_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'queries profiles and builds bounded context without transcript reconstruction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/mcp_server_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens private rooms and protects notify-all with scope and origin policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
