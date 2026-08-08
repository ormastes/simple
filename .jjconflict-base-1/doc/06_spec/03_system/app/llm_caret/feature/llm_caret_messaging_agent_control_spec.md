# LLM Caret Agent-Control Composition

This executable manual verifies that the messaging composition root owns one
provider-neutral control service for Claude, Codex, and Gemini. It does not put
provider-specific types in the messaging domain.

## Control flow

1. Create an instance-scoped messaging runtime.
2. Attach one bound session for Claude, Codex, and Gemini.
3. Inject a canonical context-manifest ID into each session.
4. Submit a task, steer the active task, and cancel it.
5. Confirm each operation succeeds through the same application boundary.

## Lifecycle flow

1. Deliver a Claude permission request and observe `waiting_input`.
2. Deliver a Codex `turn/completed` notification and observe `completed`.
3. Deliver Gemini `BeforeAgent` and observe the context receipt.
4. Attempt an unknown provider and confirm it fails closed.

## Evidence boundary

The scenario proves provider-neutral composition, session-state transitions,
and hook/App-Server event normalization using the production Simple adapters.
It does not claim that credential-backed Claude, Codex, or Gemini processes were
launched; those remain independent live integration gates.

## Source

`test/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.spl`
