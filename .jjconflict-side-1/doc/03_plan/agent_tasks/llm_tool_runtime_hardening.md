# LLM Tool Runtime Hardening - Agent Tasks

Date: 2026-07-01

## Lanes

- Codex: local/domain research, architecture/design, source patch, focused
  verification.
- Sidecar lanes: N/A for the current small diff.
- Merge owner: Codex.
- Final reviewer: highest-capability reviewer before release.

## Current Tasks

1. Restore missing source dependencies from the conflicted checkout.
2. Harden OpenCode parsing and PID kill behavior.
3. Align SGLang serve-plan args with current SGLang CLI docs.
4. Keep final requirements pending user selection from options docs.
