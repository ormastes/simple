# Kimi K3 as a Model Provider

Kimi K3 is Moonshot AI's current flagship model. This repo supports both the
Claude Code harness through `bin/k3` and Kimi's native Kimi Code harness through
the `kimi` command. Neither launcher stores an API key in the repository.

Official references: [Kimi K3 quickstart](https://platform.kimi.ai/docs/guide/kimi-k3-quickstart),
[Claude Code integration](https://platform.kimi.ai/docs/guide/claude-code-kimi),
and [Kimi Code CLI](https://github.com/MoonshotAI/kimi-code).

## Claude Code: `k3`

Create `~/.config/kimi/token` with mode `600`, or export `MOONSHOT_API_KEY` in
the current shell. Do not commit or paste the key into a launcher.

```bash
install -m 700 -d ~/.config/kimi
printf '%s' 'YOUR_MOONSHOT_API_KEY' > ~/.config/kimi/token
chmod 600 ~/.config/kimi/token
k3
```

`bin/k3` configures the official Anthropic-compatible endpoint and the complete
Claude Code mapping:

| Setting | Value |
|---------|-------|
| Endpoint | `https://api.moonshot.ai/anthropic` |
| Main and every Claude tier | `kimi-k3[1m]` |
| Subagent model | `kimi-k3[1m]` |
| Auto-compact window | `1048576` |
| Effort | `max` |

Kimi documents that every tier must be mapped; otherwise background tasks or
subagents can send an unsupported Claude model name. K3 always reasons. In the
session, `/status` must show the endpoint above and `kimi-k3[1m]`.

## Native Kimi Code harness

Install the official harness with Node.js 22.19 or newer:

```bash
npm install -g @moonshot-ai/kimi-code@latest
kimi --version
kimi
```

On first launch, run `/login` and choose Kimi Code OAuth or Kimi Platform API
key. Then use `/model` to select Kimi K3. OAuth avoids manual API-key setup;
API keys entered through `/login` remain in the harness credential store.

Kimi Code includes `coder`, `explore`, and `plan` subagents, MCP configuration,
hooks, sessions, and ACP support. Kimi recommends this native harness for K3.

## Verify

```bash
k3 -p "reply with exactly: K3_OK"
kimi -p "reply with exactly: KIMI_HARNESS_OK"
```

If `k3` reports 401, verify that the key belongs to `platform.kimi.ai` and that
no stale `ANTHROPIC_API_KEY` or model entries in `~/.claude/settings.json`
override the launcher. Do not copy the key into this repository.
