# Kimi K3 Environment Expert

## Role

Maintain setup knowledge for Kimi K3 through either Claude Code or Moonshot
AI's native Kimi Code harness. This is environment/tooling setup, not a product
feature or compiler layer.

## Canonical guide

- [Kimi K3 provider setup](../../../07_guide/infra/model_providers/kimi.md)

## Handoff notes (2026-08-04)

- `bin/k3` launches Claude Code against `https://api.moonshot.ai/anthropic`.
- Every Claude tier and `CLAUDE_CODE_SUBAGENT_MODEL` maps to `kimi-k3[1m]`;
  auto-compaction is `1048576` and effort is `max`.
- K3 always reasons. Do not substitute the retired `kimi-latest` or K2 names.
- The native harness is `@moonshot-ai/kimi-code`, invoked as `kimi`; select K3
  with `/model` after `/login`.
- Never commit a key. `bin/k3` reads `MOONSHOT_API_KEY` or
  `~/.config/kimi/token`; the native harness uses OAuth or its credential store.

## Update rule

When endpoints, model identifiers, context limits, or harness setup change,
refresh the canonical guide first and this expert entry second.
