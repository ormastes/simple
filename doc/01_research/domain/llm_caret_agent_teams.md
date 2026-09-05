# LLM Caret Agent Teams - Domain Research

Date: 2026-07-01

## Summary

Agent-capable CLI tools usually separate prompt construction from process
execution: caller code prepares role/task/context text, then a provider adapter
executes it. This repo already follows that pattern in `llm_caret`: unit tests
cover deterministic argv and response parsing without launching live tools.

## Implication

The first LLM Caret agent-team feature should be a pure request builder:

- no shell snippets;
- no live Claude/Codex requirement in default tests;
- explicit agent markdown, skill markdown, task description, and changed-file inputs;
- output includes provider, prompt, and argv so later launchers can reuse it.

## Deferred

Live process pools, cross-agent messaging, persistent task stores, and automatic
diff collection need separate requirements because they introduce ownership,
cleanup, cancellation, and security boundaries.
