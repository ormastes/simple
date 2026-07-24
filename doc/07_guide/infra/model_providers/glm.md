# GLM (Zhipu / z.ai) as a Model Provider

GLM is [Zhipu AI](https://z.ai)'s model family, exposed through the **z.ai**
endpoints. We use it as the **cheap sidecar / parallel-worker lane** — the
low-cost tier for broad SPipe lanes and mechanical fan-out work, reviewed by a
higher-capability model before done marks are accepted (see
`.claude/skills/spipe.md` "lower-model sidecars").

This guide reproduces the setup on any environment. Two tools are wired
separately because they speak different endpoints.

> **Never commit the API key.** It is a live credential. The examples below
> source it from a non-committed file or the tool's own auth store — never
> inline it into a file you might push. Mirror the `token_cmd` / `password_cmd`
> pattern the devhub facades already use for backend creds.

## 1. Get an API key

Sign in at <https://z.ai> → API keys. Keep it in a non-committed file, e.g.
`~/.config/zai/token` (mode `600`). Do not paste it into `.bashrc`, repo
configs, or anything under version control.

```bash
install -m 700 -d ~/.config/zai
printf '%s' 'YOUR_ZAI_API_KEY' > ~/.config/zai/token
chmod 600 ~/.config/zai/token
```

## 2. Claude Code (Anthropic-compatible endpoint)

Claude Code talks to any Anthropic-compatible endpoint via four env vars, then
runs `claude`. z.ai exposes an Anthropic-shaped endpoint at
`https://api.z.ai/api/anthropic`.

Add a launcher to `~/.bashrc` (or `~/.zshrc`). This form reads the token from
the file above at launch, so the secret never lives in the rc file itself:

```bash
# GLM (Zhipu) launcher for Claude Code — plain `claude` still uses your subscription
glm() {
    ANTHROPIC_BASE_URL="https://api.z.ai/api/anthropic" \
    ANTHROPIC_AUTH_TOKEN="$(cat ~/.config/zai/token)" \
    ANTHROPIC_MODEL="glm-5.2" \
    ANTHROPIC_SMALL_FAST_MODEL="glm-4.5-air" \
    claude "$@"
}
```

Then `glm` launches Claude Code against GLM; a bare `claude` still uses your
normal subscription. `ANTHROPIC_SMALL_FAST_MODEL` is the model Claude Code uses
for cheap background calls (titles, small edits) — kept on the smaller
`glm-4.5-air`.

| Env var | Value |
|---------|-------|
| `ANTHROPIC_BASE_URL` | `https://api.z.ai/api/anthropic` |
| `ANTHROPIC_AUTH_TOKEN` | your z.ai key (from the file) |
| `ANTHROPIC_MODEL` | `glm-5.2` |
| `ANTHROPIC_SMALL_FAST_MODEL` | `glm-4.5-air` |

## 3. opencode

opencode uses its own config at `~/.config/opencode/opencode.json`. GLM is added
as an OpenAI-compatible provider pointing at the z.ai **coding** endpoint
(`https://api.z.ai/api/coding/paas/v4`, distinct from the Anthropic one above):

```json
{
  "$schema": "https://opencode.ai/config.json",
  "provider": {
    "zhipuai": {
      "npm": "@ai-sdk/openai-compatible",
      "name": "Zhipu GLM (z.ai Coding)",
      "options": {
        "baseURL": "https://api.z.ai/api/coding/paas/v4"
      },
      "models": {
        "glm-5.2": {
          "name": "GLM-5.2",
          "cost": { "input": 0, "output": 0 },
          "limit": { "context": 200000, "output": 128000 }
        }
      }
    }
  },
  "model": "zhipuai/glm-5.2"
}
```

The key is **not** in this file. Supply it out-of-band so the config stays
committable/shareable:

```bash
opencode auth login          # pick zhipuai, paste the key   (preferred)
# or, per-shell:
export ZHIPUAI_API_KEY="$(cat ~/.config/zai/token)"
```

`cost: 0` reflects a flat coding-plan subscription (no per-token billing);
adjust if your plan meters tokens.

## 4. Models

| Model | Role |
|-------|------|
| `glm-5.2` | Main worker model (200k context / 128k output) |
| `glm-4.5-air` | Small/fast lane (Claude Code background calls) |

Use the names your z.ai plan actually exposes — these are the ones this
environment is configured for.

## 5. Verify

```bash
# Claude Code
glm -p "reply with exactly: GLM_OK"        # expect: GLM_OK

# opencode
opencode run "reply with exactly: GLM_OK"  # expect: GLM_OK
```

Two distinct endpoints, one key: `…/api/anthropic` for Claude Code,
`…/api/coding/paas/v4` for opencode. If Claude Code returns 401, the token file
is empty or the endpoint is the coding one by mistake; if opencode returns 401,
run `opencode auth login` for the `zhipuai` provider.

## Security recap

- Token lives in `~/.config/zai/token` (`600`), never in a committed file.
- rc-file launcher reads the token at run time; the rc file holds no secret.
- Before pushing any config change, grep the outgoing diff for the literal key —
  it must return zero hits.
