# LLM Caret Messaging Domain Contract

> This executable manual verifies the transport-neutral messaging model and the pure application policies that are available today. It demonstrates stable agent naming, canonical commands and mentions, deterministic routing, bounded previous-message context, truthful receipt labels, loop prevention, and capability-driven fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Messaging Domain Contract

This executable manual verifies the transport-neutral messaging model and the pure application policies that are available today. It demonstrates stable agent naming, canonical commands and mentions, deterministic routing, bounded previous-message context, truthful receipt labels, loop prevention, and capability-driven fallback.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | `doc/02_requirements/feature/llm_caret_messaging.md` |
| Plan | `doc/03_plan/sys_test/llm_caret_messaging.md` |
| Design | `doc/05_design/app/tools/llm_caret_messaging.md` |
| Research | `doc/01_research/app/llm_caret/messaging_platforms.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


## Overview

This executable manual verifies the transport-neutral messaging model and the
pure application policies that are available today. It demonstrates stable
agent naming, canonical commands and mentions, deterministic routing, bounded
previous-message context, truthful receipt labels, loop prevention, and
capability-driven fallback.

This is deliberately narrower than the complete messaging feature. It does not
claim primitive server, PureDatabase durability, email enrollment, hooks, MCP,
plugin installation, or live-platform interoperability evidence. Those rows
remain blocked in the system-test plan until their real production endpoints
exist; no simulator result may promote them to PASS.

**Requirements:** `doc/02_requirements/feature/llm_caret_messaging.md`

**Plan:** `doc/03_plan/sys_test/llm_caret_messaging.md`

**Design:** `doc/05_design/app/tools/llm_caret_messaging.md`

**Research:** `doc/01_research/app/llm_caret/messaging_platforms.md`

## Syntax and examples

The visible manual uses the frozen phrases `Create and bind a room`, `Route a
message to an agent`, `Inject the bounded context bundle`, and `Observe task
and receipt transitions`. Each scenario calls a public production function and
asserts its concrete result with canonical SSpec matchers. Fixtures create
canonical `RoomMessage` and `RouteCandidate` values only; they do not replace
the behavior under test.

Receipt examples always pair state with evidence. A local cursor renders as
`[read:local]`, native evidence as `[read:native]`, successful agent injection
as `[consumed]`, terminal handling as `[handled]`, and delivery failure as
`[delivery-failed]`. Capability examples select native, emulated, primitive
sidecar, or an exact unsupported error without branching on a platform name.

## Evidence boundary

The executable source imports only `messaging/domain` and
`messaging/application` modules. Passing scenarios therefore prove those pure
contracts. They do not prove network delivery, persistence across a process
restart, external human-read state, credential scope, webhook authentication,
or third-party service compatibility.

## Scenarios

### LLM Caret messaging domain and application contracts

### REQ-LLM-MSG-004: stable agent naming

#### should retain an available explicit name

- Verify: should retain an available explicit name
- Route a message to an agent
   - Expected: allocate_agent_name("Reviewer", "", "reviewer", "codex", []) equals `reviewer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should retain an available explicit name")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
expect(allocate_agent_name("Reviewer", "", "reviewer", "codex", [])).to_equal("reviewer")
```

</details>

#### should retain a persisted profile name across allocation

- Verify: should retain a persisted profile name across allocation
- Route a message to an agent
   - Expected: allocate_agent_name("", "Builder-Claude-07", "builder", "claude", []) equals `builder-claude-07`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should retain a persisted profile name across allocation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
expect(allocate_agent_name("", "Builder-Claude-07", "builder", "claude", [])).to_equal("builder-claude-07")
```

</details>

#### should reject reserved and colliding names with the lowest free ordinal

- Verify: should reject reserved and colliding names with the lowest free ordinal
- Route a message to an agent
   - Expected: agent_name_reserved("SYSTEM") is true
   - Expected: allocate_agent_name("system", "", "reviewer", "codex", ["reviewer-codex-01"]) equals `reviewer-codex-02`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should reject reserved and colliding names with the lowest free ordinal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
expect(agent_name_reserved("SYSTEM")).to_equal(true)
expect(allocate_agent_name("system", "", "reviewer", "codex", ["reviewer-codex-01"])).to_equal("reviewer-codex-02")
```

</details>

### REQ-LLM-MSG-005 and REQ-LLM-MSG-008: mentions and previous-message commands

#### should normalize canonical names and aliases

- Verify: should normalize canonical names and aliases
- Route a message to an agent
   - Expected: mentions_agent("Please ask @Reviewer-Codex-01", "reviewer-codex-01", []) is true
   - Expected: mentions_agent("Please ask @review", "reviewer-codex-01", ["review"]) is true
   - Expected: keyword_matches("Can you INSPECT this?", ["inspect"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should normalize canonical names and aliases")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
expect(mentions_agent("Please ask @Reviewer-Codex-01", "reviewer-codex-01", [])).to_equal(true)
expect(mentions_agent("Please ask @review", "reviewer-codex-01", ["review"])).to_equal(true)
expect(keyword_matches("Can you INSPECT this?", ["inspect"])).to_equal(true)
```

</details>

#### should ignore escaped and fenced mentions

- Verify: should ignore escaped and fenced mentions
- Route a message to an agent
   - Expected: mentions_agent("\\@reviewer-codex-01", "reviewer-codex-01", []) is false
   - Expected: mentions_agent("```\n@reviewer-codex-01\n```", "reviewer-codex-01", []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should ignore escaped and fenced mentions")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
expect(mentions_agent("\\@reviewer-codex-01", "reviewer-codex-01", [])).to_equal(false)
expect(mentions_agent("```\n@reviewer-codex-01\n```", "reviewer-codex-01", [])).to_equal(false)
```

</details>

#### should parse target and previous-message references

- Verify: should parse target and previous-message references
- Route a message to an agent
   - Expected: parsed.name equals `ask`
   - Expected: parsed.target equals `reviewer`
   - Expected: parsed.reference equals `^`
   - Expected: parsed.body equals `review this`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should parse target and previous-message references")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
val parsed = parse_room_command("/ask @reviewer ^ review this")
expect(parsed.name).to_equal("ask")
expect(parsed.target).to_equal("reviewer")
expect(parsed.reference).to_equal("^")
expect(parsed.body).to_equal("review this")
```

</details>

### REQ-LLM-MSG-006: deterministic main and subagent routing

#### should prefer one explicit mention before every weaker signal

- Verify: should prefer one explicit mention before every weaker signal
- Route a message to an agent
   - Expected: decision.agent_id equals `reviewer`
   - Expected: decision.reason equals `mentioned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should prefer one explicit mention before every weaker signal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
val decision = route_message([
    candidate("reviewer", AgentHandler.Subagent, true, false, false, false, false),
    candidate("builder", AgentHandler.Main, false, false, true, true, true)
])
expect(decision.agent_id).to_equal("reviewer")
expect(decision.reason).to_equal("mentioned")
```

</details>

#### should use the main handler when deterministic signals are absent

- Verify: should use the main handler when deterministic signals are absent
- Route a message to an agent
   - Expected: decision.agent_id equals `builder`
   - Expected: decision.reason equals `main_fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should use the main handler when deterministic signals are absent")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
val decision = route_message([candidate("builder", AgentHandler.Main, false, false, false, false, false)])
expect(decision.agent_id).to_equal("builder")
expect(decision.reason).to_equal("main_fallback")
```

</details>

#### should reject an ambiguous signal when no main fallback exists

- Verify: should reject an ambiguous signal when no main fallback exists
- Route a message to an agent
   - Expected: decision.agent_id equals ``
   - Expected: decision.reason equals `agent_unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should reject an ambiguous signal when no main fallback exists")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
val decision = route_message([
    candidate("one", AgentHandler.Subagent, true, false, false, false, false),
    candidate("two", AgentHandler.Advisor, true, false, false, false, false)
])
expect(decision.agent_id).to_equal("")
expect(decision.reason).to_equal("agent_unavailable")
```

</details>

### REQ-LLM-MSG-007: bounded previous context

#### should include two prior relevant messages and the trigger in chronological order

- Verify: should include two prior relevant messages and the trigger in chronological order
- Inject the bounded context bundle
   - Expected: selected.len() equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: selected[0].message_id.value equals `m-2`
   - Expected: selected[2].message_id.value equals `m-4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should include two prior relevant messages and the trigger in chronological order")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inject the bounded context bundle")
val trigger = room_message("m-4", 4, MessageOrigin.Human, "trigger", "", "", 0)
val selected = select_previous_context([
    room_message("m-1", 1, MessageOrigin.Human, "old", "", "", 0),
    room_message("m-2", 2, MessageOrigin.Human, "previous one", "", "", 0),
    room_message("m-3", 3, MessageOrigin.Human, "previous two", "", "", 0)
], trigger, 2)
expect(selected.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(selected[0].message_id.value).to_equal("m-2")
expect(selected[2].message_id.value).to_equal("m-4")
```

</details>

<details>
<summary>Advanced: should exclude status updates from room fallback context</summary>

#### should exclude status updates from room fallback context

- Verify: should exclude status updates from room fallback context
- Inject the bounded context bundle
   - Expected: selected.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: selected[0].message_id.value equals `m-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should exclude status updates from room fallback context")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inject the bounded context bundle")
val trigger = room_message("m-3", 3, MessageOrigin.Human, "trigger", "", "", 0)
val selected = select_previous_context([
    room_message("m-1", 1, MessageOrigin.Human, "question", "", "", 0),
    room_message("m-2", 2, MessageOrigin.AgentUpdate, "running", "", "builder", 0)
], trigger, 2)
expect(selected.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(selected[0].message_id.value).to_equal("m-1")
```

</details>


</details>

#### should not include messages outside the trigger thread

- Verify: should not include messages outside the trigger thread
- Inject the bounded context bundle
   - Expected: selected.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: selected[0].message_id.value equals `m-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should not include messages outside the trigger thread")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inject the bounded context bundle")
val trigger = room_message("m-4", 4, MessageOrigin.Human, "trigger", "thread-a", "", 0)
val selected = select_previous_context([
    room_message("m-1", 1, MessageOrigin.Human, "other", "thread-b", "", 0),
    room_message("m-2", 2, MessageOrigin.Human, "same", "thread-a", "", 0)
], trigger, 2)
expect(selected.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(selected[0].message_id.value).to_equal("m-2")
```

</details>

### REQ-LLM-MSG-003 and REQ-LLM-MSG-008: truthful receipt tags

#### should distinguish local and native read evidence

- Verify: should distinguish local and native read evidence
- Observe task and receipt transitions
   - Expected: receipt_tag(local) equals `[read:local]`
   - Expected: receipt_tag(native) equals `[read:native]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should distinguish local and native read evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val local = MessageReceipt(message_id: "m-1", identity_id: "human-1", state: ReceiptState.Read, evidence: ReceiptEvidence.LocalCursor, occurred_at: 1, detail: "")
val native = MessageReceipt(message_id: "m-1", identity_id: "human-1", state: ReceiptState.Read, evidence: ReceiptEvidence.Native, occurred_at: 2, detail: "")
expect(receipt_tag(local)).to_equal("[read:local]")
expect(receipt_tag(native)).to_equal("[read:native]")
```

</details>

#### should distinguish agent consumption from terminal handling

- Verify: should distinguish agent consumption from terminal handling
- Observe task and receipt transitions
   - Expected: receipt_tag(consumed) equals `[consumed]`
   - Expected: receipt_tag(handled) equals `[handled]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should distinguish agent consumption from terminal handling")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val consumed = MessageReceipt(message_id: "m-1", identity_id: "agent-1", state: ReceiptState.ConsumedByAgent, evidence: ReceiptEvidence.Synthetic, occurred_at: 1, detail: "")
val handled = MessageReceipt(message_id: "m-1", identity_id: "agent-1", state: ReceiptState.Handled, evidence: ReceiptEvidence.Synthetic, occurred_at: 2, detail: "")
expect(receipt_tag(consumed)).to_equal("[consumed]")
expect(receipt_tag(handled)).to_equal("[handled]")
```

</details>

#### should expose delivery failure without presenting it as read

- Verify: should expose delivery failure without presenting it as read
- Observe task and receipt transitions
   - Expected: receipt_tag(failed) equals `[delivery-failed]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should expose delivery failure without presenting it as read")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
val failed = MessageReceipt(message_id: "m-1", identity_id: "human-1", state: ReceiptState.Failed, evidence: ReceiptEvidence.Unknown, occurred_at: 1, detail: "rate limit")
expect(receipt_tag(failed)).to_equal("[delivery-failed]")
```

</details>

### REQ-LLM-MSG-014: loop prevention

#### should allow a fresh human trigger

- Verify: should allow a fresh human trigger
- Route a message to an agent
   - Expected: decision.allowed is true
   - Expected: decision.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should allow a fresh human trigger")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
val decision = loop_guard(room_message("m-1", 1, MessageOrigin.Human, "build", "", "", 0), "builder", false, 4, false)
expect(decision.allowed).to_equal(true)
expect(decision.reason).to_equal("ok")
```

</details>

#### should reject mirrored self messages and duplicate events

- Verify: should reject mirrored self messages and duplicate events
- Route a message to an agent
   - Expected: loop_guard(message, "builder", false, 4, false).reason equals `self_mirror`
   - Expected: loop_guard(message, "reviewer", true, 4, false).reason equals `duplicate_event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should reject mirrored self messages and duplicate events")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
val message = room_message("m-1", 1, MessageOrigin.AgentAnswer, "done", "", "builder", 1)
expect(loop_guard(message, "builder", false, 4, false).reason).to_equal("self_mirror")
expect(loop_guard(message, "reviewer", true, 4, false).reason).to_equal("duplicate_event")
```

</details>

#### should reject progress triggers and exhausted handoffs

- Verify: should reject progress triggers and exhausted handoffs
- Route a message to an agent
   - Expected: loop_guard(progress, "reviewer", false, 4, false).reason equals `progress_non_triggering`
   - Expected: loop_guard(exhausted, "reviewer", false, 4, false).reason equals `handoff_limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should reject progress triggers and exhausted handoffs")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Route a message to an agent")
val progress = room_message("m-1", 1, MessageOrigin.AgentUpdate, "running", "", "builder", 1)
expect(loop_guard(progress, "reviewer", false, 4, false).reason).to_equal("progress_non_triggering")
val exhausted = room_message("m-2", 2, MessageOrigin.AgentAnswer, "handoff", "", "builder", 4)
expect(loop_guard(exhausted, "reviewer", false, 4, false).reason).to_equal("handoff_limit")
```

</details>

### REQ-LLM-MSG-017: capability-driven fallback

#### should select native, emulated, and primitive-sidecar actions from capability truth

- Verify: should select native, emulated, and primitive-sidecar actions from capability truth
- Create and bind a room
   - Expected: plan_capability_fallback(CapabilityLevel.Native, "private_message").action equals `native:private_message`
   - Expected: plan_capability_fallback(CapabilityLevel.Emulated, "thread").action equals `emulated:thread`
   - Expected: plan_capability_fallback(CapabilityLevel.PrimitiveSidecar, "room_create").action equals `primitive_sidecar:room_create`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should select native, emulated, and primitive-sidecar actions from capability truth")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
expect(plan_capability_fallback(CapabilityLevel.Native, "private_message").action).to_equal("native:private_message")
expect(plan_capability_fallback(CapabilityLevel.Emulated, "thread").action).to_equal("emulated:thread")
expect(plan_capability_fallback(CapabilityLevel.PrimitiveSidecar, "room_create").action).to_equal("primitive_sidecar:room_create")
```

</details>

#### should return an exact capability error for unsupported behavior

- Verify: should return an exact capability error for unsupported behavior
- Create and bind a room
   - Expected: plan.action equals ``
   - Expected: plan.error equals `capability_not_supported:private_message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should return an exact capability error for unsupported behavior")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
val plan = plan_capability_fallback(CapabilityLevel.Unsupported, "private_message")
expect(plan.action).to_equal("")
expect(plan.error).to_equal("capability_not_supported:private_message")
```

</details>

#### should expose stable serialized capability level names

- Verify: should expose stable serialized capability level names
- Create and bind a room
   - Expected: capability_level_name(CapabilityLevel.Native) equals `native`
   - Expected: capability_level_name(CapabilityLevel.PrimitiveSidecar) equals `primitive_sidecar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should expose stable serialized capability level names")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
expect(capability_level_name(CapabilityLevel.Native)).to_equal("native")
expect(capability_level_name(CapabilityLevel.PrimitiveSidecar)).to_equal("primitive_sidecar")
```

</details>

### Supporting evidence: typed identifier validation

#### should normalize the identifier kind and reject empty or spaced values

- Verify: should normalize the identifier kind and reject empty or spaced values
- Create and bind a room
   - Expected: valid.kind equals `room`
   - Expected: messaging_id_valid(valid) is true
   - Expected: messaging_id_valid(MessagingId(kind: "room", value: "room 1")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-004 REQ-LLM-MSG-005 REQ-LLM-MSG-008 REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-003 REQ-LLM-MSG-014 REQ-LLM-MSG-017
step("Verify: should normalize the identifier kind and reject empty or spaced values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
val valid = messaging_id(" ROOM ", "room-1")
expect(valid.kind).to_equal("room")
expect(messaging_id_valid(valid)).to_equal(true)
expect(messaging_id_valid(MessagingId(kind: "room", value: "room 1"))).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `c255c6d32ec822e8a72873762e61b01daacfd015a30ef20f1d134c1abb6b51e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c255c6d32ec822e8a72873762e61b01daacfd015a30ef20f1d134c1abb6b51e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c255c6d32ec822e8a72873762e61b01daacfd015a30ef20f1d134c1abb6b51e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain an available explicit name' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain a persisted profile name across allocation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject reserved and colliding names with the lowest free ordinal' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl:119:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize canonical names and aliases' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl:128:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should ignore escaped and fenced mentions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl:136:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse target and previous-message references' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
