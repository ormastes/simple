# core_policy_spec

> Core messaging policy stays transport-neutral, deterministic, and truthful.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# core_policy_spec

Core messaging policy stays transport-neutral, deterministic, and truthful.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/core_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Core messaging policy stays transport-neutral, deterministic, and truthful.

## Scenarios

### LLM Caret messaging core policy

#### validates tagged IDs and allocates stable collision-free agent names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates tagged IDs and allocates stable collision-free agent names
- Validate canonical typed IDs and reserve control names
   - Expected: messaging_id_valid(messaging_id("agent", "agent-01")) is true
   - Expected: messaging_id_valid(messaging_id("agent", "")) is false
   - Expected: agent_name_reserved("SYSTEM") is true
- Prefer an available explicit name, then persisted name, then the lowest ordinal
   - Expected: allocate_agent_name("Reviewer", "", "reviewer", "codex", []) equals `reviewer`
   - Expected: allocate_agent_name("system", "Saved-Agent", "reviewer", "codex", []) equals `saved-agent`
   - Expected: allocate_agent_name("", "", "reviewer", "codex", ["Reviewer-Codex-01"]) equals `reviewer-codex-02`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("validates tagged IDs and allocates stable collision-free agent names")
step("Validate canonical typed IDs and reserve control names")
expect(messaging_id_valid(messaging_id("agent", "agent-01"))).to_equal(true)
expect(messaging_id_valid(messaging_id("agent", ""))).to_equal(false)
expect(agent_name_reserved("SYSTEM")).to_equal(true)

step("Prefer an available explicit name, then persisted name, then the lowest ordinal")
expect(allocate_agent_name("Reviewer", "", "reviewer", "codex", [])).to_equal("reviewer")
expect(allocate_agent_name("system", "Saved-Agent", "reviewer", "codex", [])).to_equal("saved-agent")
expect(allocate_agent_name("", "", "reviewer", "codex", ["Reviewer-Codex-01"])).to_equal("reviewer-codex-02")
```

</details>

#### parses commands and ignores escaped or fenced mentions

- parses commands and ignores escaped or fenced mentions
- Parse explicit agent and previous-message targeting
   - Expected: command.name equals `ask`
   - Expected: command.target equals `reviewer`
   - Expected: command.reference equals `^`
   - Expected: command.body equals `review this`
- Normalize visible mentions without treating examples as triggers
   - Expected: mentions_agent("please ask @Reviewer", "reviewer", []) is true
   - Expected: mentions_agent("escaped \\@reviewer", "reviewer", []) is false
   - Expected: mentions_agent("```\n@reviewer\n```", "reviewer", []) is false
   - Expected: keyword_matches("Please INSPECT this", ["inspect"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses commands and ignores escaped or fenced mentions")
step("Parse explicit agent and previous-message targeting")
val command = parse_room_command("/ask @reviewer ^ review this")
expect(command.name).to_equal("ask")
expect(command.target).to_equal("reviewer")
expect(command.reference).to_equal("^")
expect(command.body).to_equal("review this")

step("Normalize visible mentions without treating examples as triggers")
expect(mentions_agent("please ask @Reviewer", "reviewer", [])).to_equal(true)
expect(mentions_agent("escaped \\@reviewer", "reviewer", [])).to_equal(false)
expect(mentions_agent("```\n@reviewer\n```", "reviewer", [])).to_equal(false)
expect(keyword_matches("Please INSPECT this", ["inspect"])).to_equal(true)
```

</details>

#### plans native, emulated, sidecar, and unsupported behavior from capability data

- plans native, emulated, sidecar, and unsupported behavior from capability data
- Select behavior without branching on a platform name
   - Expected: plan_capability_fallback(CapabilityLevel.Native, "private_message").action equals `native:private_message`
   - Expected: plan_capability_fallback(CapabilityLevel.Emulated, "reply").action equals `emulated:reply`
   - Expected: plan_capability_fallback(CapabilityLevel.PrimitiveSidecar, "room_create").action equals `primitive_sidecar:room_create`
   - Expected: plan_capability_fallback(CapabilityLevel.Unsupported, "mark_read").error equals `capability_not_supported:mark_read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("plans native, emulated, sidecar, and unsupported behavior from capability data")
step("Select behavior without branching on a platform name")
expect(plan_capability_fallback(CapabilityLevel.Native, "private_message").action).to_equal("native:private_message")
expect(plan_capability_fallback(CapabilityLevel.Emulated, "reply").action).to_equal("emulated:reply")
expect(plan_capability_fallback(CapabilityLevel.PrimitiveSidecar, "room_create").action).to_equal("primitive_sidecar:room_create")
expect(plan_capability_fallback(CapabilityLevel.Unsupported, "mark_read").error).to_equal("capability_not_supported:mark_read")
```

</details>

#### routes deterministically before falling back to the main agent

- routes deterministically before falling back to the main agent
- An explicit mention wins over owner and main fallback
   - Expected: decision.agent_id equals `reviewer`
   - Expected: decision.reason equals `mentioned`
- Ambiguous capability matches do not invoke a selector implicitly
   - Expected: route_message([c1, c2]).agent_id equals `two`
   - Expected: route_message([]).reason equals `agent_unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes deterministically before falling back to the main agent")
step("An explicit mention wins over owner and main fallback")
val mentioned = RouteCandidate(agent_id: "reviewer", handler: AgentHandler.Subagent,
    mentioned: true, replied_to: false, assigned: false, capability_match: false, room_owner: false)
val main = RouteCandidate(agent_id: "builder", handler: AgentHandler.Main,
    mentioned: false, replied_to: false, assigned: false, capability_match: false, room_owner: true)
val decision = route_message([mentioned, main])
expect(decision.agent_id).to_equal("reviewer")
expect(decision.reason).to_equal("mentioned")

step("Ambiguous capability matches do not invoke a selector implicitly")
val c1 = RouteCandidate(agent_id: "one", handler: AgentHandler.Advisor,
    mentioned: false, replied_to: false, assigned: false, capability_match: true, room_owner: false)
val c2 = RouteCandidate(agent_id: "two", handler: AgentHandler.Main,
    mentioned: false, replied_to: false, assigned: false, capability_match: true, room_owner: false)
expect(route_message([c1, c2]).agent_id).to_equal("two")
expect(route_message([]).reason).to_equal("agent_unavailable")
```

</details>

#### selects two prior relevant messages and excludes unrelated progress

- selects two prior relevant messages and excludes unrelated progress
- Select prior non-status room messages in chronological order
   - Expected: selected.len() equals `3`
   - Expected: selected[0].message_id.value equals `m1`
   - Expected: selected[1].message_id.value equals `m3`
   - Expected: selected[2].message_id.value equals `m4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("selects two prior relevant messages and excludes unrelated progress")
step("Select prior non-status room messages in chronological order")
val first = message("m1", 1, "first", MessageOrigin.Human, "", "", 0)
val update = message("m2", 2, "working", MessageOrigin.AgentUpdate, "", "builder", 0)
val second = message("m3", 3, "second", MessageOrigin.AgentAnswer, "", "builder", 0)
val trigger = message("m4", 4, "trigger", MessageOrigin.Human, "", "", 0)
val selected = select_previous_context([first, update, second], trigger, 2)
expect(selected.len()).to_equal(3)
expect(selected[0].message_id.value).to_equal("m1")
expect(selected[1].message_id.value).to_equal("m3")
expect(selected[2].message_id.value).to_equal("m4")
```

</details>

<details>
<summary>Advanced: reports truthful receipt evidence and prevents agent feedback loops</summary>

#### reports truthful receipt evidence and prevents agent feedback loops

- reports truthful receipt evidence and prevents agent feedback loops
- Keep native human read evidence distinct from local cursors
   - Expected: receipt_tag(native_read) equals `[read:native]`
   - Expected: receipt_tag(local_read) equals `[read:local]`
- Reject duplicate, self, exhausted, and implicit progress triggers
   - Expected: loop_guard(human, "reviewer", true, 4, false).reason equals `duplicate_event`
   - Expected: loop_guard(self_message, "reviewer", false, 4, false).reason equals `self_mirror`
   - Expected: loop_guard(message("m4", 4, "handoff", MessageOrigin.Human, "", "", 4), "reviewer", false, 4, false).reason equals `handoff_limit`
   - Expected: loop_guard(progress, "reviewer", false, 4, false).reason equals `progress_non_triggering`
   - Expected: loop_guard(progress, "reviewer", false, 4, true).allowed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports truthful receipt evidence and prevents agent feedback loops")
step("Keep native human read evidence distinct from local cursors")
val native_read = MessageReceipt(message_id: "m1", identity_id: "i1", state: ReceiptState.Read,
    evidence: ReceiptEvidence.Native, occurred_at: 1, detail: "")
val local_read = MessageReceipt(message_id: "m1", identity_id: "i1", state: ReceiptState.Read,
    evidence: ReceiptEvidence.LocalCursor, occurred_at: 1, detail: "")
expect(receipt_tag(native_read)).to_equal("[read:native]")
expect(receipt_tag(local_read)).to_equal("[read:local]")

step("Reject duplicate, self, exhausted, and implicit progress triggers")
val human = message("m1", 1, "hello", MessageOrigin.Human, "", "", 0)
val self_message = message("m2", 2, "echo", MessageOrigin.AgentAnswer, "", "reviewer", 0)
val progress = message("m3", 3, "working", MessageOrigin.AgentUpdate, "", "builder", 0)
expect(loop_guard(human, "reviewer", true, 4, false).reason).to_equal("duplicate_event")
expect(loop_guard(self_message, "reviewer", false, 4, false).reason).to_equal("self_mirror")
expect(loop_guard(message("m4", 4, "handoff", MessageOrigin.Human, "", "", 4), "reviewer", false, 4, false).reason).to_equal("handoff_limit")
expect(loop_guard(progress, "reviewer", false, 4, false).reason).to_equal("progress_non_triggering")
expect(loop_guard(progress, "reviewer", false, 4, true).allowed).to_equal(true)
```

</details>


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
- `REQ-LLM-MSG-004`
- `REQ-LLM-MSG-005`
- `REQ-LLM-MSG-006`
- `REQ-LLM-MSG-007`
- `REQ-LLM-MSG-008`
- `REQ-LLM-MSG-014`
- `REQ-LLM-MSG-017`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb83370bca6e94fd0ed92ccbaeb5fe886fd79d5d420d3c2d3b5eb76c644eb683`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb83370bca6e94fd0ed92ccbaeb5fe886fd79d5d420d3c2d3b5eb76c644eb683`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb83370bca6e94fd0ed92ccbaeb5fe886fd79d5d420d3c2d3b5eb76c644eb683`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/core_policy_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/core_policy_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/core_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/core_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/core_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/core_policy_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 9 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/core_policy_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates tagged IDs and allocates stable collision-free agent names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/core_policy_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses commands and ignores escaped or fenced mentions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/core_policy_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans native, emulated, sidecar, and unsupported behavior from capability data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
