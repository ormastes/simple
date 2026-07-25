# GLM (Zhipu / z.ai) Environment Expert

## Role

Maintain how-to knowledge for running this repo's tooling against **GLM**
(Zhipu AI, via the z.ai endpoints) as the cheap sidecar / parallel-worker
model. Use this entry when setting GLM up on a new machine or when a session
needs the low-cost lane wired for Claude Code or opencode.

This is an `env_expert` entry — environment/tooling setup, not a compiler layer
(`layer_expert/`) or product feature (`feature_expert/`).

## Links

- [Full setup guide](../../../07_guide/infra/model_providers/glm.md) — env vars,
  alias, opencode provider JSON, key handling, verification (**canonical**)
- [SPipe skill: lower-model sidecars](../../../../.claude/skills/spipe.md) —
  where GLM fits in the tiered worker/review flow

## Handoff Notes (2026-07-24)

- **Two endpoints, one key.** Claude Code → `https://api.z.ai/api/anthropic`
  (Anthropic-compatible; env vars `ANTHROPIC_BASE_URL` / `ANTHROPIC_AUTH_TOKEN`
  / `ANTHROPIC_MODEL=glm-5.2` / `ANTHROPIC_SMALL_FAST_MODEL=glm-4.5-air`, then
  `claude`). opencode → `https://api.z.ai/api/coding/paas/v4` (OpenAI-compatible
  provider `zhipuai`, model `zhipuai/glm-5.2`). Do not cross the endpoints.
- **Key never in a committed file.** Source it from `~/.config/zai/token` (600)
  at launch, or from the tool's own auth store (`opencode auth login`). Same
  discipline as the devhub `token_cmd`/`password_cmd` backend-cred pattern.
- **Role:** GLM is the cheap fan-out/worker tier; a higher-capability model still
  reviews before done marks — see the SPipe sidecar rule.

## Update Rule

If the endpoints, model names, or key-handling change, refresh the canonical
guide first, then this entry, before committing.
