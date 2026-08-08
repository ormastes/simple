---
name: llm-caret-messaging
description: Collaborate through canonical Simple rooms with durable tasks, bounded context, truthful receipts, private rooms, and artifacts.
---

# LLM Caret Messaging

Use the `llm-caret-messaging` MCP server for intentional chat actions. Prefer
canonical room and task IDs returned by tools; do not invent transport IDs.

1. Use `chat_who` before assigning work when the responsible agent is unclear.
2. Use `chat_open_private` for private content; never copy it into a public room.
3. Use `chat_assign` for stateful work and `chat_task_update` only on significant
   transitions: running, waiting input, blocked, completed, failed, or canceled.
4. Call `chat_get_context` with a stable `context_bundle_id` before injecting
   room context. Cite canonical message IDs in replies.
5. Publish durable outputs with `chat_publish_artifact` instead of embedding
   large reports or patches in progress messages.
6. Treat local cursors as local evidence. Never claim a native human read unless
   the transport supplies native evidence.
7. Progress updates do not wake other agents unless a human explicitly replies
   or assigns a task.

Lifecycle hooks only enqueue local events. They must return promptly and must
not contain transport credentials or call external chat APIs directly.
