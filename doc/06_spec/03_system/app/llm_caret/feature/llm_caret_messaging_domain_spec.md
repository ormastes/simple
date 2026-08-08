# LLM Caret Messaging Domain Contract

> Executable evidence for the currently implemented transport-neutral domain
> and pure application policies. Server, persistence, plugin, MCP, hooks, and
> live-platform rows remain blocked rather than simulated as passing behavior.

**Requirements:** [LLM Caret messaging requirements](../../../../../../../02_requirements/feature/llm_caret_messaging.md)

**Plan:** [LLM Caret messaging system-test plan](../../../../../../../03_plan/sys_test/llm_caret_messaging.md)

**Design:** [LLM Caret messaging design](../../../../../../../05_design/app/tools/llm_caret_messaging.md)

**Research:** [Messaging-platform research](../../../../../../../01_research/app/llm_caret/messaging_platforms.md)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

## Overview

This manual verifies stable agent naming, canonical command and mention
parsing, deterministic main/subagent routing, bounded previous-message context,
truthful receipt evidence, loop prevention, and capability-driven fallback.
Every expected value comes from a public production function in the executable
[SSpec source](../../../../../../../test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl).

## Reading the scenarios

The flow uses the frozen manual steps `Create and bind a room`, `Route a
message to an agent`, `Inject the bounded context bundle`, and `Observe task
and receipt transitions`. Receipt state and evidence are separate: a local
cursor never masquerades as a platform-native read, and consumption never
masquerades as terminal handling.

## Claim boundary

These passing scenarios do not prove primitive server, PureDatabase, account
enrollment, hook execution, MCP discovery, plugin installation, or any live
transport. The system-test plan records those as planned or blocked until their
real production seams and, for external services, credential-backed evidence
exist.

## Scenario manual

### REQ-LLM-MSG-004 — Stable agent naming

1. **Retain an available explicit name.** Route a message to an agent and
   verify `Reviewer` normalizes to `reviewer`.
2. **Retain a persisted profile name.** Verify `Builder-Claude-07` remains
   `builder-claude-07` across allocation.
3. **Recover from reserved names and collisions.** Verify `SYSTEM` is reserved
   and an occupied `reviewer-codex-01` advances to `reviewer-codex-02`.

### REQ-LLM-MSG-005 and REQ-LLM-MSG-008 — Mentions and commands

1. **Normalize canonical names, aliases, and keywords.** Route a message to an
   agent and verify case-insensitive canonical, alias, and keyword matches.
2. **Ignore escaped and fenced mentions.** Verify escaped text and fenced code
   do not wake the agent.
3. **Parse previous-message commands.** Verify `/ask @reviewer ^ review this`
   yields command `ask`, target `reviewer`, reference `^`, and the exact body.

### REQ-LLM-MSG-006 — Deterministic routing

1. **Prefer an explicit mention.** Verify a uniquely mentioned subagent wins
   before assignment, capability, owner, or main fallback signals.
2. **Use the main fallback.** Verify a main handler is selected when no
   deterministic signal is present.
3. **Reject ambiguity.** Verify two mentioned non-main candidates yield
   `agent_unavailable` instead of an arbitrary selection.

### REQ-LLM-MSG-007 — Bounded previous context

1. **Include two prior messages.** Inject the bounded context bundle and verify
   two preceding relevant messages plus the trigger remain chronological.
2. **Exclude status chatter.** Verify an `AgentUpdate` is omitted from room
   fallback context.
3. **Respect thread boundaries.** Verify messages from another thread are not
   selected.

### REQ-LLM-MSG-003 and REQ-LLM-MSG-008 — Truthful receipts

1. **Distinguish read evidence.** Observe task and receipt transitions and
   verify local and native evidence render `[read:local]` and `[read:native]`.
2. **Distinguish consumption and handling.** Verify successful injection is
   `[consumed]` while terminal task handling is `[handled]`.
3. **Expose delivery failure.** Verify a failed delivery renders
   `[delivery-failed]`, never a read label.

### REQ-LLM-MSG-014 — Loop prevention

1. **Allow a fresh human trigger.** Route a new human message and verify the
   decision is allowed with reason `ok`.
2. **Reject self mirrors and duplicates.** Verify the guard returns
   `self_mirror` and `duplicate_event` for those independent conditions.
3. **Reject progress triggers and exhausted handoffs.** Verify unaddressed
   `AgentUpdate` messages and messages at the hop limit do not trigger agents.

### REQ-LLM-MSG-017 — Capability-driven fallback

1. **Select declared behavior.** Create and bind a room and verify native,
   emulated, and primitive-sidecar capability levels select their matching
   actions.
2. **Reject unsupported behavior exactly.** Verify unsupported private
   messaging returns `capability_not_supported:private_message`.
3. **Serialize stable capability names.** Verify `native` and
   `primitive_sidecar` names are stable and platform-neutral.

### Supporting evidence — Typed identifiers

1. **Normalize and validate identifiers.** Create and bind a room, verify the
   kind is trimmed and lowercased, accept `room-1`, and reject a spaced value.

<details>
<summary>Executable SSpec</summary>

The complete executable source is retained at
`test/03_system/app/llm_caret/feature/llm_caret_messaging_domain_spec.spl`.
It contains the canonical `step("...")` calls and all 22 concrete assertions;
no placeholder, pending, or synthetic-success helper is used.

</details>
