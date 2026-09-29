# Kimi K3 as a Model Provider

Kimi K3 can run through Claude Code or Moonshot AI's native Kimi Code harness.
The Kimi Code subscription and Moonshot Open Platform are separate account and
credential systems. A valid key returns `401 Invalid Authentication` when it is
sent to the other system, so choose the endpoint from where the key was issued,
not from its spelling or prefix.

Official references: [Kimi Code overview](https://www.kimi.com/code/docs/en/),
[Claude Code integration](https://www.kimi.com/code/docs/en/third-party-tools/claude-code.html),
[Kimi K3 quickstart](https://platform.kimi.ai/docs/guide/kimi-k3-quickstart),
and [Kimi Code CLI](https://github.com/MoonshotAI/kimi-code).

## Provider matrix

| Credential source | Claude/Anthropic endpoint | Claude model | Native/OpenAI endpoint | Native model |
|---|---|---|---|---|
| Kimi Code Console / subscription | `https://api.kimi.com/coding/` (global login: `https://api.kimi.ai/coding/`) | `k3[1m]` | `https://api.kimi.com/coding/v1` (global: `https://api.kimi.ai/coding/v1`) | `k3` |
| `platform.kimi.ai` Open Platform | `https://api.moonshot.ai/anthropic` | `kimi-k3[1m]` | `https://api.moonshot.ai/v1` | `kimi-k3` |

The bracketed `[1m]` spelling is a Claude Code environment-variable convention.
Use the unbracketed model ID in the native harness and ordinary API requests.
Kimi Code subscription availability and the 1M window depend on membership.

## Credential storage

Never commit or paste a key into a launcher. Store a user-private token with
mode `600`, or use the native harness credential flow:

```bash
install -m 700 -d ~/.config/kimi
printf '%s' 'YOUR_KIMI_KEY' > ~/.config/kimi/token
chmod 600 ~/.config/kimi/token
```

Because that token file does not identify its issuing platform, a launcher must
still select the matching endpoint explicitly, which is why `bin/k3` treats that
file as an Open Platform key. A Kimi Code Console *key* must use the
subscription mapping below. A Kimi Code *login* needs no key file: see `bin/k3`.

## Claude Code harness

For a Kimi Code Console/subscription key:

```bash
export ANTHROPIC_BASE_URL='https://api.kimi.com/coding/'
export ANTHROPIC_API_KEY="$(sed -n '1p' ~/.config/kimi/token)"
export ANTHROPIC_MODEL='k3[1m]'
export ANTHROPIC_DEFAULT_FABLE_MODEL="$ANTHROPIC_MODEL"
export ANTHROPIC_DEFAULT_OPUS_MODEL="$ANTHROPIC_MODEL"
export ANTHROPIC_DEFAULT_SONNET_MODEL="$ANTHROPIC_MODEL"
export ANTHROPIC_DEFAULT_HAIKU_MODEL="$ANTHROPIC_MODEL"
export CLAUDE_CODE_SUBAGENT_MODEL="$ANTHROPIC_MODEL"
export CLAUDE_CODE_AUTO_COMPACT_WINDOW=1048576
export CLAUDE_CODE_MAX_CONTEXT_TOKENS=1048576
export CLAUDE_CODE_EFFORT_LEVEL=max
claude
```

`bin/k3` maps every Claude tier and subagent to K3, sets the 1M compaction
window, and uses max effort. It picks the first credential it finds:

1. `MOONSHOT_API_KEY`: Open Platform, `kimi-k3[1m]`.
2. A Kimi Code login in `~/.kimi-code` (run `kimi` once and log in):
   subscription endpoint, `k3[1m]`. Region follows the login (`oauth_host`
   `auth.kimi.ai` means `api.kimi.ai`, otherwise `api.kimi.com`). The OAuth access
   token lives only 900s, so `k3` passes `bin/kimi-code-token` to Claude Code as
   `apiKeyHelper` (re-run every 10 min). The helper does the same
   `refresh_token` grant as the `kimi` CLI and writes the rotated tokens back
   to the same credentials file, so `kimi` stays logged in.
3. `~/.config/kimi/token`: Open Platform, `kimi-k3[1m]`.

In `/status`, the base URL and model must match the selected row above.

## Native Kimi Code harness

Install the official harness with Node.js 22.19 or newer:

```bash
npm install -g @moonshot-ai/kimi-code@latest
kimi --version
kimi
```

Use `/login` for Kimi Code OAuth or a Kimi Open Platform key, then `/model` to
select K3. A static Kimi Code Console key can instead use a private
`~/.kimi-code/config.toml` provider whose `base_url` is
`https://api.kimi.com/coding/v1`, model is `k3`, and context size is `1048576`.
Keep that config mode `600` because it contains the key.

Launch modes:

```bash
kimi                 # normal approval flow
kimi --yolo          # approve regular tool calls automatically
kimi --auto          # fully autonomous permission mode
```

Kimi Code auto-discovers a project `.mcp.json`. If MCP startup fails, inspect
that file before changing the harness: stale absolute checkout paths are a
common cause. A status of `connecting` is not PASS. Wait for every required
server to report `connected`, and probe a real tool call when the server has a
known compiled-vs-source behavior difference.

Inside tmux, `extended-keys` being off affects modified Enter combinations,
not ordinary Enter. Enable it for the live server and persist it:

```bash
tmux set -g extended-keys on
printf '%s\n' 'set -g extended-keys on' >> ~/.tmux.conf
```

## Verify once

```bash
k3 -p "reply with exactly: K3_OK"
kimi -p "reply with exactly: KIMI_HARNESS_OK"
```

Do not repeat a green probe. On `401`, compare the credential source and both
endpoint/model cells in the provider matrix. Also remove stale
`ANTHROPIC_API_KEY`, `ANTHROPIC_AUTH_TOKEN`, or model overrides that can take
precedence over the launcher.
