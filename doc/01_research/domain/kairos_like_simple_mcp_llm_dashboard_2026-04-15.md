<!-- codex-research -->
# KAIROS-Like Simple MCP + LLM Dashboard — Domain Research

Date: 2026-04-15
Scope: public Claude Code capabilities and adjacent patterns relevant to a KAIROS-like assistant architecture for Simple.

## Research Rule

This document separates:

- **Verified public behavior** from official Claude Code docs
- **Inferred design direction** based on those public features
- **Unverified / leaked KAIROS claims**, which should not be copied directly into Simple requirements without independent justification

## What Public Claude Code Now Confirms

### 1. Remote session attachment is publicly real

Verified public docs:

- Remote Control runs a session on the user’s machine and exposes it through web/mobile surfaces.
- Local MCP servers, tools, and project configuration remain available in that mode.
- A single interactive process supports one remote session unless server mode is used; server mode can host multiple concurrent sessions.

Sources:

- Claude Code Remote Control docs: `claude --remote-control`, `/remote-control`, local execution model, server mode, concurrent capacity, and limitations.

Design takeaway for Simple:

- “viewer/client attached to a persistent local session” is now a public, validated pattern.
- Simple should support local session ownership with optional remote or dashboard attachment, not a web-only or dashboard-only assistant.

### 2. Periodic proactive work is publicly real

Verified public docs:

- Claude Code supports `/loop` and cron-style scheduled prompts inside a session.
- Session-scoped tasks live only while the session exists.
- Public docs explicitly separate session-scoped scheduling from durable scheduling on cloud/desktop/CI surfaces.

Sources:

- Claude Code scheduled tasks docs.

Design takeaway for Simple:

- A periodic tick loop is a supported interaction model, but it should be explicit, rate-limited, and lifecycle-aware.
- Simple should distinguish between:
  - session-scoped loop
  - durable local daemon schedule
  - externally triggered events

### 3. External event push into a running session is publicly real

Verified public docs:

- Claude Code Channels can push chat messages, webhooks, CI failures, and monitoring events into a running local session.
- A channel is modeled as an MCP server that emits channel notifications to Claude Code.
- Public docs position Channels as the event-driven alternative to timer polling.

Sources:

- Claude Code channels docs
- Claude Code channels reference

Design takeaway for Simple:

- A KAIROS-like design should not be timer-only.
- The Simple assistant core should accept both:
  - periodic ticks
  - pushed external signals

### 4. Background tasks and background hooks are publicly real

Verified public docs:

- Claude Code can run hook commands asynchronously in the background.
- Background hook results can later deliver context/system messages into the session.
- Desktop UI exposes a tasks pane for background work such as subagents and background commands.

Sources:

- Claude Code hooks docs
- Claude Code desktop docs

Design takeaway for Simple:

- The correct UX is not “background work is invisible.”
- Background tasks should have visible state, output, stop controls, and result delivery paths.

### 5. Subagents with separate context are publicly real

Verified public docs:

- Claude Code supports specialized subagents with separate context windows.
- Agent hooks can spawn subagents that investigate with tools and return structured decisions.

Sources:

- Claude Code subagents docs
- Claude Code hooks docs

Design takeaway for Simple:

- “spawn agents” is not a fringe feature. It is now a practical public pattern.
- The Simple implementation should support delegated bounded subtasks with explicit ownership, visibility, and merge-back results.

### 6. Session memory and resumability are publicly real, but bounded

Verified public docs:

- Claude Code stores session transcripts locally as JSONL and supports continue/resume/fork flows.
- Auto memory exists, but is bounded and distinct from full conversation history.

Sources:

- How Claude Code works

Design takeaway for Simple:

- Simple should prefer bounded durable memory:
  - session transcripts
  - derived briefs/digests
  - explicit retained facts
- It should avoid promising magical unconstrained long-term memory.

## Public Feature Map Relevant to “KAIROS-Like”

| Desired trait | Public Claude Code analogue | What this suggests for Simple |
|---|---|---|
| Persistent local assistant | Remote Control + local sessions | Keep execution local-first |
| Viewer/client semantics | Remote Control web/mobile attachment | Let dashboard attach to live session |
| Periodic wakeups | `/loop` and scheduled tasks | Add explicit tick engine |
| Event-driven wakeups | Channels | Add push-signal intake path |
| Background task execution | Async hooks + Desktop tasks pane | Add visible worker/task state |
| Delegated sub-work | Subagents | Add spawn-agent orchestration |
| Brief summaries | Output styles + session summaries | Add brief/digest mode |
| Memory continuity | resume/fork + auto memory | Use bounded digests, not opaque memory lore |

## What Is Still Not Publicly Proven About “KAIROS”

As of 2026-04-15, I could verify public Claude Code documentation for:

- Remote Control
- scheduled tasks and `/loop`
- Channels
- hooks
- subagents
- desktop background task monitoring

I did **not** find official public documentation proving an Anthropic feature called `KAIROS` with:

- a documented `claude assistant` command
- a documented `autoDream` subsystem
- official append-only daily memory logs as a named product feature
- a public daemon mode specifically branded as KAIROS

Interpretation:

- Some earlier “KAIROS” reporting may have described internal or pre-release concepts.
- But many of the important behaviors once discussed as KAIROS-like are now publicly present under other names.

## Recommended Requirements Direction for Simple

Do not define the feature as “clone KAIROS.”

Define it as a Simple-native capability family:

### A. Assistant Core

- local-first persistent session
- tick scheduler
- signal/event inbox
- pause/resume/brief/ack controls

### B. Delegation Core

- explicit spawned subtasks
- separate child context/state
- bounded contracts for handoff and result merge

### C. Observation Core

- append-only timeline of wakes, decisions, actions, failures, and summaries
- operator-visible background work
- structured notification log

### D. Surface Split

- `simple mcp` as programmable control plane
- `llm dashboard` as visual operations plane
- combined live mode when both are present

## Non-Functional Guidance From Public Patterns

1. Make autonomy explicit.
Public Claude features expose whether behavior is session-scoped, cloud-hosted, remote-controlled, or event-driven. Simple should do the same.

2. Keep background work interruptible and inspectable.
Desktop task panes, hook output, and session control all reinforce visibility.

3. Prefer multiple wake mechanisms.
Polling alone is weaker than polling plus external signal push.

4. Treat persistence as layered.
Transcript, digest, retained facts, and control state should be separate layers with different retention policies.

5. Support remote or alternate surfaces without changing where execution happens.
Remote Control demonstrates that “remote interface” and “remote execution” are different concerns.

## Sources

Official Claude Code docs used:

- Remote Control: https://code.claude.com/docs/en/remote-control
- Scheduled tasks: https://code.claude.com/docs/en/scheduled-tasks
- Channels: https://code.claude.com/docs/en/channels
- Channels reference: https://code.claude.com/docs/en/channels-reference
- Hooks: https://code.claude.com/docs/en/hooks
- Subagents: https://code.claude.com/docs/en/sub-agents
- Desktop: https://code.claude.com/docs/en/desktop
- How Claude Code works: https://code.claude.com/docs/en/how-claude-code-works
- MCP: https://code.claude.com/docs/en/mcp
- Output styles: https://code.claude.com/docs/en/output-styles

## Conclusion

The best current interpretation is:

- “KAIROS” itself is not something I can treat as a public product contract.
- But the public Claude Code product now validates most of the architectural ideas that matter:
  - local persistent sessions
  - attached remote viewers
  - scheduled and event-driven wakeups
  - background work visibility
  - delegated subagents

That is enough evidence to design a strong Simple-native equivalent without depending on leaks.
