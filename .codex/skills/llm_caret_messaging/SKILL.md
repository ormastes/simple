---
name: llm-caret-messaging
description: "Use the canonical LLM Caret room, tasks, profiles, agent routing, receipts, and messaging MCP with Claude, Codex, and Gemini integrations."
---

# LLM Caret Messaging

Use this skill for agent chat, room context, task handoff, profiles, receipts,
or transport bridging. The primitive Simple room is authoritative. Never treat
an LLM provider, external platform, or the legacy `AgentTeamMailbox` as the
domain owner.

## MCP flow

1. Discover identity and room state with `chat_who` and `chat_read`.
2. Join only when membership is required with `chat_join`.
3. Read an injection-safe bundle with `chat_get_context`; do not reconstruct it
   from an unbounded transcript.
4. Use `chat_assign` for a stateful task and `chat_task_update` only for
   significant transitions: queued, running, waiting_input, blocked, completed,
   failed, canceled.
5. Publish durable outputs using `chat_publish_artifact`, then respond using
   `chat_send` with the same correlation/task reference.
6. Advance `chat_mark_read` only after consumption. Preserve its evidence level:
   native, local_cursor, synthetic, or unknown.

Every mutating call that accepts an idempotency key must receive a stable key.
An `agent_update` does not trigger another agent unless a human explicitly
replies or assigns it. Never mirror private-room content to a public room.

## Routing and context

Route deterministically: explicit mention, reply target, `/assign`, unique
capability match, room owner, optional selector, then main-agent fallback.
Context includes the trigger, reply chain, previous two relevant messages,
addressed unread messages, profiles, active task, artifacts, and optional source
pack within the configured budget. Apply ACL and redaction before injection.

## Installation safety

Use `caret messaging plugin install --agents ...` and `plugin check`. The
`simple caret ...` alias is equivalent after the root CLI has been rebuilt with
the Caret command registration.
The installer merges settings and records ownership/hashes. Do not edit agent
settings manually, copy credentials into hooks, or delete entries during
uninstall when their current hash differs from the installed hash.
