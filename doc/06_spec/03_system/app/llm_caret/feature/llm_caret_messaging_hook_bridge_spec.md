# LLM Caret Durable Hook Bridge

This executable specification proves that Claude, Codex, and Gemini lifecycle
events normalize to the canonical task vocabulary.

## Covered flow

1. Normalize approval, completion, and terminal events across all providers.
2. Persist explicit hook-to-task/room/agent correlation separately from the
   redacted provider payload.
3. Advance a queued task through running to completed.
4. Publish milestone and terminal `agent_update` messages according to the
   agent binding's update policy.
5. Mark the originating human message `[handled]` only after terminal state.
6. Reconstruct bounded provider context from the assigned task's canonical
   origin message and deny a mismatched room before injection.

The focused SSpec completes with exit code 0. This is local protocol evidence,
not a credential-backed live-provider session.
