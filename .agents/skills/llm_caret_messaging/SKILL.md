---
name: llm-caret-messaging
description: "Collaborate through canonical LLM Caret rooms, task routing, context bundles, profiles, receipts, and artifacts."
---

# LLM Caret Messaging Agent Protocol

Use the messaging MCP for intentional collaboration. Inspect `chat_who`, read
with `chat_read`, and obtain bounded authorized input with `chat_get_context`.
Create work through `chat_assign`; report meaningful state transitions through
`chat_task_update`; attach durable results with `chat_publish_artifact`; send the
answer with `chat_send` using stable correlation and idempotency identifiers.

Do not awaken agents from progress updates, trigger yourself from mirrored
messages, claim a native human read from a local cursor, include unrelated
private-room messages, or repeatedly handle the same `(message_id, binding_id)`.
Use `chat_open_private` for confidential discussion and `chat_notify_all` only
when explicitly requested and permitted.

The primitive room defines semantics. A transport capability may be native,
emulated, primitive_sidecar, or unsupported; follow the reported capability and
fallback plan rather than branching on a platform name.
