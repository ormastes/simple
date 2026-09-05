---
name: llm-caret-messaging
description: Collaborate through LLM Caret rooms and synchronize Claude lifecycle events with canonical tasks.
---

# LLM Caret Messaging for Claude

Use `chat_who` and `chat_read` to orient, then `chat_get_context` for the bounded
ACL-checked context bundle. Use `chat_assign`, `chat_task_update`,
`chat_publish_artifact`, and `chat_send` for task collaboration. Preserve task,
correlation, causation, and idempotency identifiers.

Claude hooks are lifecycle synchronization, not transport workers. They enqueue
SessionStart, prompt, tool, subagent, stop, and session-end events locally and
return promptly. The bridge owns external delivery and retries. Never put
transport credentials in hook configuration.

Progress updates do not wake agents by default. Private messages stay in a
canonical direct room. A local read cursor is reported as local evidence, never
as a platform-native human read receipt.
