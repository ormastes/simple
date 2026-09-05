# primitive_service_spec

> Primitive services expose deterministic mutations for the pure-Simple SQL adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# primitive_service_spec

Primitive services expose deterministic mutations for the pure-Simple SQL adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/primitive_service_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Primitive services expose deterministic mutations for the pure-Simple SQL adapter.

## Scenarios

### primitive LLM Caret application services

<details>
<summary>Advanced: creates rooms with owner membership and enforces private membership</summary>

#### creates rooms with owner membership and enforces private membership

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates rooms with owner membership and enforces private membership
- Create a private room and atomically project its owner
   - Expected: created.accepted is true
   - Expected: created.memberships.len() equals `1`
   - Expected: created.memberships[0].role equals `owner`
   - Expected: identity_can_read(created.room, created.memberships, "human-2") is false
- Membership addition is idempotent and grants private-room access
   - Expected: joined.memberships.len() equals `2`
   - Expected: duplicate.memberships.len() equals `2`
   - Expected: identity_can_read(created.room, joined.memberships, "human-2") is true
- Direct rooms require two distinct identities
   - Expected: create_direct_room("dm1", "w1", "human-1", "human-1", 12).error equals `direct_room_requires_two_identities`
   - Expected: direct.accepted is true
   - Expected: direct.memberships.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("creates rooms with owner membership and enforces private membership")
step("Create a private room and atomically project its owner")
val created = create_room("r1", "w1", RoomKind.Private, "review", "code review", "private",
    "mention", "milestones", "default", "human-1", 10)
expect(created.accepted).to_equal(true)
expect(created.memberships.len()).to_equal(1)
expect(created.memberships[0].role).to_equal("owner")
expect(identity_can_read(created.room, created.memberships, "human-2")).to_equal(false)

step("Membership addition is idempotent and grants private-room access")
val joined = add_room_member(created.room, created.memberships, "human-2", "member", 11)
val duplicate = add_room_member(created.room, joined.memberships, "human-2", "member", 12)
expect(joined.memberships.len()).to_equal(2)
expect(duplicate.memberships.len()).to_equal(2)
expect(identity_can_read(created.room, joined.memberships, "human-2")).to_equal(true)

step("Direct rooms require two distinct identities")
expect(create_direct_room("dm1", "w1", "human-1", "human-1", 12).error).to_equal("direct_room_requires_two_identities")
val direct = create_direct_room("dm1", "w1", "human-1", "agent-1", 12)
expect(direct.accepted).to_equal(true)
expect(direct.memberships.len()).to_equal(2)
```

</details>


</details>

#### prepares accepted messages, bounded history, and truthful local cursors

- prepares accepted messages, bounded history, and truthful local cursors
- Reject an empty body before persistence
   - Expected: rejected.error equals `message_body_required`
- Produce the canonical message and acceptance receipt for storage
   - Expected: accepted.accepted is true
   - Expected: accepted.message.body equals `hello`
   - Expected: accepted.message.room_seq equals `2`
   - Expected: accepted.receipt.detail equals `server_accepted`
- Page only the requested room after its sequence cursor
   - Expected: history.len() equals `1`
   - Expected: history[0].message_id.value equals `m3`
- Reject cursor claims beyond the canonical room sequence
   - Expected: advance_read_cursor("r1", "human-1", 4, 3).error equals `cursor_out_of_range`
   - Expected: advance_read_cursor("r1", "human-1", 3, 3).accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("prepares accepted messages, bounded history, and truthful local cursors")
step("Reject an empty body before persistence")
val rejected = prepare_message("m0", "w1", "r1", 1, "human-1", "", MessageOrigin.Human,
    "  ", "", "", "c0", "", 0, 10)
expect(rejected.error).to_equal("message_body_required")

step("Produce the canonical message and acceptance receipt for storage")
val accepted = prepare_message("m1", "w1", "r1", 2, "human-1", "", MessageOrigin.Human,
    " hello ", "", "", "c1", "", 0, 11)
expect(accepted.accepted).to_equal(true)
expect(accepted.message.body).to_equal("hello")
expect(accepted.message.room_seq).to_equal(2)
expect(accepted.receipt.detail).to_equal("server_accepted")

step("Page only the requested room after its sequence cursor")
val history = history_after([room_message("m1", "r1", 1, "one"),
    room_message("other", "r2", 2, "other"), room_message("m3", "r1", 3, "three")], "r1", 1, 10)
expect(history.len()).to_equal(1)
expect(history[0].message_id.value).to_equal("m3")

step("Reject cursor claims beyond the canonical room sequence")
expect(advance_read_cursor("r1", "human-1", 4, 3).error).to_equal("cursor_out_of_range")
expect(advance_read_cursor("r1", "human-1", 3, 3).accepted).to_equal(true)
```

</details>

#### answers profile queries and emits structured join events

- answers profile queries and emits structured join events
- Resolve an agent by a case-insensitive alias
   - Expected: lookup.found is true
   - Expected: profile_summary(lookup.profile) contains `State: running`
- Announce stable identity, role, capabilities, and current task
   - Expected: announcement.origin equals `MessageOrigin.System`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("answers profile queries and emits structured join events")
step("Resolve an agent by a case-insensitive alias")
val profile = AgentProfile(agent_id: messaging_id("agent", "reviewer-1"), display_name: "Reviewer-Codex-01",
    aliases: ["review"], provider: "codex", role_summary: "code review", capabilities: ["Simple", "tests"],
    current_task_id: "T-9", status: AgentStatus.Running, owner_identity_id: "human-1",
    room_ids: ["r1"], last_activity_at: 20)
val lookup = find_agent_profile([profile], "REVIEW")
expect(lookup.found).to_equal(true)
expect(profile_summary(lookup.profile).contains("State: running")).to_equal(true)

step("Announce stable identity, role, capabilities, and current task")
val announcement = agent_join_announcement(profile, "w1", "r1", "join-1", 4, 21)
expect(announcement.body).to_contain("Reviewer-Codex-01 joined")
expect(announcement.body).to_contain("Capabilities: Simple, tests")
expect(announcement.origin).to_equal(MessageOrigin.System)
```

</details>

<details>
<summary>Advanced: keeps task lifecycle distinct from room messages and terminal states final</summary>

#### keeps task lifecycle distinct from room messages and terminal states final

- keeps task lifecycle distinct from room messages and terminal states final
- Create a queued task from one origin message
   - Expected: created.accepted is true
   - Expected: created.task.state equals `TaskState.Queued`
- Require explicit requested input for waiting state
   - Expected: missing.error equals `required_input_missing`
   - Expected: waiting.accepted is true
   - Expected: approved.task.state equals `TaskState.Running`
- Reject attempts to restart a terminal task
   - Expected: completed.task.completed_at equals `33`
   - Expected: transition_task(completed.task, TaskState.Running, "again", "", 34).error equals `task_already_terminal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps task lifecycle distinct from room messages and terminal states final")
step("Create a queued task from one origin message")
val created = create_task("T-1", "m1", "builder-1", "implement the service", 30)
expect(created.accepted).to_equal(true)
expect(created.task.state).to_equal(TaskState.Queued)

step("Require explicit requested input for waiting state")
val missing = transition_task(created.task, TaskState.WaitingInput, "needs approval", "", 31)
expect(missing.error).to_equal("required_input_missing")
val waiting = transition_task(created.task, TaskState.WaitingInput, "needs approval", "approve network", 31)
expect(waiting.accepted).to_equal(true)
val approved = approve_task(waiting.task, 32)
expect(approved.task.state).to_equal(TaskState.Running)

step("Reject attempts to restart a terminal task")
val completed = transition_task(approved.task, TaskState.Completed, "done", "", 33)
expect(completed.task.completed_at).to_equal(33)
expect(transition_task(completed.task, TaskState.Running, "again", "", 34).error).to_equal("task_already_terminal")
```

</details>


</details>

#### requires notify-all permission and never fans out progress updates

- requires notify-all permission and never fans out progress updates
- Allow a human room owner but reject unprivileged and agent-update broadcasts
   - Expected: notify_all_allowed(["room_owner"], MessageOrigin.Human) is true
   - Expected: notify_all_allowed([], MessageOrigin.Human) is false
   - Expected: notify_all_allowed(["notify_all"], MessageOrigin.AgentUpdate) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires notify-all permission and never fans out progress updates")
step("Allow a human room owner but reject unprivileged and agent-update broadcasts")
expect(notify_all_allowed(["room_owner"], MessageOrigin.Human)).to_equal(true)
expect(notify_all_allowed([], MessageOrigin.Human)).to_equal(false)
expect(notify_all_allowed(["notify_all"], MessageOrigin.AgentUpdate)).to_equal(false)
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
- `REQ-LLM-MSG-002`
- `REQ-LLM-MSG-003`
- `REQ-LLM-MSG-008`
- `REQ-LLM-MSG-009`
- `REQ-LLM-MSG-010`
- `REQ-LLM-MSG-011`
- `REQ-LLM-MSG-014`
- `REQ-LLM-MSG-015`
- `REQ-LLM-MSG-016`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f57cc0421d62abaf50a32dab102f973f1eb0b885f5dac783908a8a5fd63ffbeb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f57cc0421d62abaf50a32dab102f973f1eb0b885f5dac783908a8a5fd63ffbeb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f57cc0421d62abaf50a32dab102f973f1eb0b885f5dac783908a8a5fd63ffbeb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/primitive_service_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/primitive_service_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/primitive_service_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/primitive_service_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/primitive_service_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/primitive_service_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 10 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/primitive_service_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates rooms with owner membership and enforces private membership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/primitive_service_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prepares accepted messages, bounded history, and truthful local cursors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/primitive_service_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers profile queries and emits structured join events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
