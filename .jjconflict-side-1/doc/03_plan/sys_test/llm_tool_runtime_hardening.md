# LLM Tool Runtime Hardening - Test Plan

Date: 2026-07-01

## Existing Focused Tests

- OpenCode arg construction and prompt-last ordering.
- OpenCode attach args without shell kill shortcuts.
- OpenCode JSON content and `sessionID` parsing.
- OpenCode invalid PID kill guard.
- vLLM static serve-plan redaction and backend-native flags.
- SGLang static serve-plan redaction and backend-native flags.

## Deferred System Tests

Live tests should stay opt-in until requirements select a live gate:

- installed `opencode` binary smoke
- OpenCode server attach smoke
- vLLM server startup smoke
- SGLang server startup smoke

Default CI should keep using static unit specs because live tests need external
tools, credentials, ports, models, and GPU/runtime resources.
