# Fork Oh My Codex And Update Hook Flag Plan

## Goal

Create or update a personal fork of `Yeachan-Heo/oh-my-codex` so your fork carries the current Codex hook feature behavior: use `[features].hooks = true`, keep legacy `codex_hooks` only as compatibility for old Codex CLIs, and preserve original/user hook commands in `hooks.json`.

## Current Evidence

- Installed Codex CLI reports `hooks` as the stable feature.
- Upstream `Yeachan-Heo/oh-my-codex` `main` already contains source support for canonical `hooks` plus legacy `codex_hooks` migration.
- Direct push to upstream failed because the repo is not owned by `ormastes`.

## Steps

1. Fork upstream to the user account:
   ```bash
   gh repo fork Yeachan-Heo/oh-my-codex --clone=false
   ```

2. Clone or reuse the fork:
   ```bash
   git clone https://github.com/ormastes/oh-my-codex.git ~/dev/pub/oh-my-codex
   cd ~/dev/pub/oh-my-codex
   git remote add upstream https://github.com/Yeachan-Heo/oh-my-codex.git
   ```

3. Rebase fork `main` onto upstream:
   ```bash
   git fetch upstream
   git checkout main
   git rebase upstream/main
   ```

4. Push only to the personal fork:
   ```bash
   env -u GITHUB_TOKEN git push origin main
   ```

5. Reinstall from the fork when ready:
   ```bash
   npm install -g ~/dev/pub/oh-my-codex
   omx setup --force
   ```

## Validation

Run in the fork:

```bash
npm run build
node --test dist/config/__tests__/codex-feature-flags.test.js \
  dist/config/__tests__/generator-notify.test.js \
  dist/config/__tests__/codex-hooks.test.js \
  dist/cli/__tests__/setup-hooks-shared-ownership.test.js
codex features list | rg '^hooks\\s+stable\\s+true'
rg -n '^codex_hooks\\s*=' ~/.codex/config.toml
```

Expected result: tests pass, `hooks` is stable and true, and `~/.codex/config.toml` has no `codex_hooks` assignment.

## Risks

- `GITHUB_TOKEN` may be invalid and override GitHub CLI auth; use `env -u GITHUB_TOKEN` for git push.
- If the fork has custom commits, rebase conflicts should preserve upstream hook-flag logic and local unrelated changes.
- Do not push to `Yeachan-Heo/oh-my-codex`; push to `ormastes/oh-my-codex`.
