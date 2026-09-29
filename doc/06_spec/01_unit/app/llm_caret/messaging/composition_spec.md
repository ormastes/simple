# composition_spec

> Purpose: Prove that LLM Caret messaging composition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# composition_spec

Purpose: Prove that LLM Caret messaging composition.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/composition_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that LLM Caret messaging composition.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### LLM Caret messaging composition

<details>
<summary>Advanced: should persist a canonical room message through the runtime</summary>

#### should persist a canonical room message through the runtime

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should persist a canonical room message through the runtime
- Verify: should persist a canonical room message through the runtime
   - Expected: runtime.ready() is true
   - Expected: room.accepted is true
   - Expected: sent.ok is true
   - Expected: sent.room_seq equals `1`
   - Expected: messages.len() equals `1`
   - Expected: messages[0].body equals `hello agents`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should persist a canonical room message through the runtime")
step("Verify: should persist a canonical room message through the runtime")
# @req: REQ-APP-LLM-CARET-001
var runtime = MessagingRuntime.memory()
expect(runtime.ready()).to_equal(true)
val room = runtime.create_canonical_room("dev", "workspace", RoomKind.Channel, "Development",
    "", "public", "room", "human-1", 1)
expect(room.accepted).to_equal(true)
val sent = runtime.send_message("m-1", "workspace", "dev", "human-1", "", MessageOrigin.Human,
    "hello agents", "", "corr-1", "", 0, 2, "idem-message-1")
expect(sent.ok).to_equal(true)
expect(sent.room_seq).to_equal(1)  # oracle: 1 — named expected value from the requirement
val messages = runtime.read_messages("dev", "human-1", 0, 10)
expect(messages.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(messages[0].body).to_equal("hello agents")
```

</details>


</details>

<details>
<summary>Advanced: should isolate canonical direct rooms</summary>

#### should isolate canonical direct rooms

- should isolate canonical direct rooms
- Verify: should isolate canonical direct rooms
   - Expected: runtime.open_direct_room("dm", "workspace", "human-1", "agent-owner", 1).accepted is true
   - Expected: runtime.read_messages("dm", "outsider", 0, 10).len() equals `0`
   - Expected: runtime.read_messages("dm", "agent-owner", 0, 10).len() equals `1`
   - Expected: runtime.store.identity("human-1").kind equals `IdentityKind.Human`
   - Expected: runtime.store.identity("agent-owner").kind equals `IdentityKind.Human`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should isolate canonical direct rooms")
step("Verify: should isolate canonical direct rooms")
var runtime = MessagingRuntime.memory()
expect(runtime.open_direct_room("dm", "workspace", "human-1", "agent-owner", 1).accepted).to_equal(true)
expect(runtime.send_message("m-1", "workspace", "dm", "human-1", "", MessageOrigin.Human,
    "private", "", "corr", "", 0, 2, "idem-private-1").ok).to_equal(true)
expect(runtime.read_messages("dm", "outsider", 0, 10).len()).to_equal(0)
expect(runtime.read_messages("dm", "agent-owner", 0, 10).len()).to_equal(1)
expect(runtime.store.identity("human-1").kind).to_equal(IdentityKind.Human)
expect(runtime.store.identity("agent-owner").kind).to_equal(IdentityKind.Human)
```

</details>


</details>

#### should project an agent identity when an API-created profile is bound

- should project an agent identity when an API-created profile is bound
- Verify: should project an agent identity when an API-created profile is bound
   - Expected: runtime.register_profile(profile).accepted is true
   - Expected: runtime.register_agent_binding("gemini", agent_binding).ok is true
   - Expected: runtime.store.identity("agent-api").kind equals `IdentityKind.Agent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should project an agent identity when an API-created profile is bound")
step("Verify: should project an agent identity when an API-created profile is bound")
var runtime = MessagingRuntime.memory()
expect(runtime.create_canonical_room("agent-room", "workspace", RoomKind.Channel,
    "Agents", "", "public", "mention", "human-1", 1).accepted).to_equal(true)
val profile = AgentProfile(agent_id: messaging_id("agent", "agent-api"),
    display_name: "reviewer-gemini-01", aliases: ["reviewer"], provider: "gemini",
    role_summary: "review", capabilities: ["Simple"], current_task_id: "",
    status: AgentStatus.Idle, owner_identity_id: "human-1", room_ids: [],
    last_activity_at: 2)
expect(runtime.register_profile(profile).accepted).to_equal(true)
val agent_binding = AgentBinding(binding_id: messaging_id("agent_binding", "binding-api"),
    room_id: messaging_id("room", "agent-room"), agent_id: messaging_id("agent", "agent-api"),
    handler: AgentHandler.Subagent, session_policy: "persistent_per_thread",
    trigger_policy: "mention", update_policy: "milestones", context_policy: "bounded",
    permissions: ["room:read"])
expect(runtime.register_agent_binding("gemini", agent_binding).ok).to_equal(true)
expect(runtime.store.identity("agent-api").kind).to_equal(IdentityKind.Agent)
```

</details>

<details>
<summary>Advanced: should route a room message into a task and consumed context</summary>

#### should route a room message into a task and consumed context

- should route a room message into a task and consumed context
- Verify: should route a room message into a task and consumed context
   - Expected: runtime.register_profile(profile).accepted is true
   - Expected: runtime.register_agent_binding("claude", agent_binding).ok is true
   - Expected: routed.routed is true
   - Expected: routed.agent_id equals `builder`
   - Expected: routed.task_id equals `task-route-me`
   - Expected: runtime.tasks.len() equals `1`
   - Expected: runtime.store.context_manifest_count() equals `1`
   - Expected: receipts[receipts.len() - 1].identity_id equals `builder`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should route a room message into a task and consumed context")
step("Verify: should route a room message into a task and consumed context")
var runtime = MessagingRuntime.memory()
expect(runtime.create_canonical_room("routed-room", "workspace", RoomKind.Channel,
    "Routed", "", "public", "room", "human-1", 1).accepted).to_equal(true)
val profile = AgentProfile(agent_id: messaging_id("agent", "builder"),
    display_name: "builder-claude-01", aliases: ["builder"], provider: "claude",
    role_summary: "implementation", capabilities: ["Simple"], current_task_id: "",
    status: AgentStatus.Idle, owner_identity_id: "human-1", room_ids: ["routed-room"],
    last_activity_at: 2)
expect(runtime.register_profile(profile).accepted).to_equal(true)
val agent_binding = AgentBinding(binding_id: messaging_id("agent_binding", "binding-builder"),
    room_id: messaging_id("room", "routed-room"), agent_id: messaging_id("agent", "builder"),
    handler: AgentHandler.Main, session_policy: "persistent_per_room",
    trigger_policy: "room", update_policy: "milestones", context_policy: "bounded",
    permissions: ["room:read", "room:write"])
expect(runtime.register_agent_binding("claude", agent_binding).ok).to_equal(true)
expect(runtime.send_message("route-me", "workspace", "routed-room", "human-1", "",
    MessageOrigin.Human, "Implement the feature", "", "corr-route", "", 0, 3,
    "route-message-key").ok).to_equal(true)
val routed = runtime.route_human_message("route-me", "builder", 4)
expect(routed.routed).to_equal(true)
expect(routed.agent_id).to_equal("builder")
expect(routed.task_id).to_equal("task-route-me")
expect(runtime.tasks.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(runtime.store.context_manifest_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val receipts = runtime.store.receipts("route-me")
expect(receipts[receipts.len() - 1].identity_id).to_equal("builder")
```

</details>


</details>

#### should recover ACL, profile, and task projections after restart

- should recover ACL, profile, and task projections after restart
- Verify: should recover ACL, profile, and task projections after restart
   - Expected: runtime.open_direct_room("restart-dm", "workspace", "human-1", "agent-1", 1).accepted is true
   - Expected: runtime.register_profile(profile).accepted is true
   - Expected: runtime.register_agent_binding("claude", agent_binding).ok is true
   - Expected: runtime.assign_task("task-1", "origin-1", "agent-1", "Implement restart", 3).accepted is true
   - Expected: runtime.advance_transport_cursors("slack-binding", "event-7", "171.2").accepted is true
   - Expected: runtime.close() is true
   - Expected: recovered_messages.len() equals `1`
   - Expected: recovered_messages[0].body equals `bridge me`
   - Expected: runtime.who("builder").found is true
   - Expected: runtime.tasks.len() equals `1`
   - Expected: runtime.tasks[0].objective equals `Implement restart`
   - Expected: runtime.store.workspace("workspace").name equals `workspace`
   - Expected: runtime.store.identity("human-1").kind equals `IdentityKind.Human`
   - Expected: runtime.store.identity("agent-1").kind equals `IdentityKind.Agent`
   - Expected: runtime.store.task_events("task-1").len() equals `1`
   - Expected: runtime.store.task_events("task-1")[0].state equals `queued`
   - Expected: runtime.bindings.len() equals `1`
   - Expected: runtime.bindings[0].agent_id.value equals `agent-1`
   - Expected: runtime.transport_binding("slack-binding").external_room_id equals `D123`
   - Expected: runtime.transport_binding("slack-binding").last_inbound_cursor equals `event-7`
   - Expected: runtime.external_message_ref("slack-binding", "transport-message").external_message_id equals `171.2`
   - Expected: runtime.external_message_ref("slack-binding", "transport-message").external_thread_id equals `171.1`
   - Expected: recovered_delivery.len() equals `1`
   - Expected: recovered_delivery[0].credential_ref equals `secret://slack/development`
   - Expected: runtime.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should recover ACL, profile, and task projections after restart")
step("Verify: should recover ACL, profile, and task projections after restart")
val path = "/tmp/llm_caret_composition_restart_" + getpid().to_text() + ".db"
file_delete(path)
var runtime = MessagingRuntime.open(path)
expect(runtime.open_direct_room("restart-dm", "workspace", "human-1", "agent-1", 1).accepted).to_equal(true)
val profile = AgentProfile(agent_id: messaging_id("agent", "agent-1"), display_name: "builder-claude-01",
    aliases: ["builder"], provider: "claude", role_summary: "implementation",
    capabilities: ["Simple", "tests"], current_task_id: "", status: AgentStatus.Idle,
    owner_identity_id: "human-1", room_ids: ["restart-dm"], last_activity_at: 2)
expect(runtime.register_profile(profile).accepted).to_equal(true)
val agent_binding = AgentBinding(binding_id: messaging_id("agent_binding", "binding-agent-1"),
    room_id: messaging_id("room", "restart-dm"), agent_id: messaging_id("agent", "agent-1"),
    handler: AgentHandler.Main, session_policy: "persistent_per_room",
    trigger_policy: "mention", update_policy: "milestones", context_policy: "bounded",
    permissions: ["room:read", "room:write"])
expect(runtime.register_agent_binding("claude", agent_binding).ok).to_equal(true)
expect(runtime.assign_task("task-1", "origin-1", "agent-1", "Implement restart", 3).accepted).to_equal(true)
expect(runtime.send_message("transport-message", "workspace", "restart-dm", "human-1", "",
    MessageOrigin.Human, "bridge me", "", "transport-correlation", "", 0, 4,
    "transport-idempotency").ok).to_equal(true)
expect(runtime.bind_transport("slack-binding", "restart-dm", "slack", "D123", "full",
    "slack-v1").accepted).to_equal(true)
expect(runtime.map_external_message("slack-binding:transport-message", "slack-binding",
    "transport-message", "171.2", "171.1", 5).accepted).to_equal(true)
expect(runtime.advance_transport_cursors("slack-binding", "event-7", "171.2").accepted).to_equal(true)
val request_template = CredentialHttpRequestTemplate(accepted: true, method: "POST",
    url_template: "https://slack.com/api/chat.postMessage",
    headers: ["Content-Type: application/json"], body: "{}",
    credential_ref: "secret://slack/development", credential_mode: "bearer",
    idempotency_key: "stable-runtime-delivery", error: "")
expect(runtime.queue_transport_template("runtime-delivery", "transport-message",
    "slack-binding", request_template, 6).accepted).to_equal(true)
expect(runtime.close()).to_equal(true)

runtime = MessagingRuntime.open(path)
val recovered_messages = runtime.read_messages("restart-dm", "agent-1", 0, 10)
expect(recovered_messages.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(recovered_messages[0].body).to_equal("bridge me")
expect(runtime.who("builder").found).to_equal(true)
expect(runtime.tasks.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(runtime.tasks[0].objective).to_equal("Implement restart")
expect(runtime.store.workspace("workspace").name).to_equal("workspace")
expect(runtime.store.identity("human-1").kind).to_equal(IdentityKind.Human)
expect(runtime.store.identity("agent-1").kind).to_equal(IdentityKind.Agent)
expect(runtime.store.task_events("task-1").len()).to_equal(1)
expect(runtime.store.task_events("task-1")[0].state).to_equal("queued")
expect(runtime.bindings.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(runtime.bindings[0].agent_id.value).to_equal("agent-1")
expect(runtime.transport_binding("slack-binding").external_room_id).to_equal("D123")
expect(runtime.transport_binding("slack-binding").last_inbound_cursor).to_equal("event-7")
expect(runtime.external_message_ref("slack-binding", "transport-message").external_message_id).to_equal("171.2")
expect(runtime.external_message_ref("slack-binding", "transport-message").external_thread_id).to_equal("171.1")
val recovered_delivery = runtime.store.queued_transport_requests(100, 10)
expect(recovered_delivery.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(recovered_delivery[0].credential_ref).to_equal("secret://slack/development")
expect(runtime.close()).to_equal(true)
file_delete(path)
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

- `REQ-SSPEC-APP`
- `REQ-APP-LLM-CARET-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a57440a3b052610a495a992118e04a6fc338a6418ee368a98af1feb641a6642b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a57440a3b052610a495a992118e04a6fc338a6418ee368a98af1feb641a6642b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a57440a3b052610a495a992118e04a6fc338a6418ee368a98af1feb641a6642b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/app/llm_caret/messaging/composition_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/composition_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/messaging/composition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/composition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should persist a canonical room message through the runtime' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should persist a canonical room message through the runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should isolate canonical direct rooms' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should isolate canonical direct rooms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should project an agent identity when an API-created profile is bound' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should project an agent identity when an API-created profile is bound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route a room message into a task and consumed context' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/messaging/composition_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recover ACL, profile, and task projections after restart' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
