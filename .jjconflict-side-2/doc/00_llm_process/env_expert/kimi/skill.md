# Kimi K3 Environment Expert

## Role

Maintain setup knowledge for Kimi K3 through either Claude Code or Moonshot
AI's native Kimi Code harness. This is environment/tooling setup, not a product
feature or compiler layer.

## Canonical guide

- [Kimi K3 provider setup](../../../07_guide/infra/model_providers/kimi.md)

## Handoff notes (2026-08-04)

- Kimi Code subscription keys and Moonshot Open Platform keys are independent.
  Choose the endpoint from the issuing console; a cross-platform key returns
  `401 Invalid Authentication` even when the key itself is valid.
- Kimi Code subscription: Claude uses `https://api.kimi.com/coding/` with
  `k3[1m]`; the native harness uses `https://api.kimi.com/coding/v1` with `k3`.
- Moonshot Open Platform: Claude uses `https://api.moonshot.ai/anthropic` with
  `kimi-k3[1m]`; repo `bin/k3` implements this mapping today.
- Map every Claude tier and `CLAUDE_CODE_SUBAGENT_MODEL`; set both compaction and
  maximum context to `1048576`. K3 supports `low`, `high`, and `max` effort.
- The native harness is `@moonshot-ai/kimi-code`: `kimi`, `kimi --yolo`, or
  `kimi --auto`. It auto-discovers project `.mcp.json` files.
- For MCP failure, check stale absolute paths first. The current Simple LSP MCP
  source lane needs `bin/simple run ...` through `bin/mcp_stdio_bridge.js`; its
  cached native artifact connects but fails `tools/call` argument extraction.
- A tmux `extended-keys` warning affects modified Enter keys. Enable it with
  `tmux set -g extended-keys on` and persist the same line in `~/.tmux.conf`.
- Never commit a key. Private token and native config files must be mode `600`.

## Update rule

When endpoints, model identifiers, context limits, or harness setup change,
refresh the canonical guide first and this expert entry second.
