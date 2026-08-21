# LLM Caret Agent Backends

## Purpose

Prove the provider-neutral Caret agent runtime recognizes and launches Claude,
Codex, Gemini, and Kimi CLI processes without silently falling back to another
provider.

## Build provider launch plans

Claude retains its `-p` and JSON-output plan; Codex retains `exec <prompt>`.
Gemini and Kimi use the generic agent prompt plan and resolve their own explicit
binary paths through `agent_command_for_provider_with_all`.

## Launch, poll, and stop each provider

The system scenario uses `/bin/echo` as each provider executable so it exercises
the real spawn, poll, and stop ownership path without paid API calls. Every
launch must return a positive PID and `started`; polling may observe running or
already exited; stopping may report stopped or the expected already-exited
error.

## Scope boundary

This proves Caret wrapper/process ownership, not live provider authentication or
model correctness. Local vLLM launch is a separate strict bootstrap gate.
smux multi-Caret supervision remains TODO until a production adapter connects
the smux session/pane lifecycle to `AgentTeamProcess`.
