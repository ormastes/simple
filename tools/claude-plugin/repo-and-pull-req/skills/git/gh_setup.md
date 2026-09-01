# GitHub Setup Skill

Interactive setup for GitHub CLI (`gh`) integration.

## Prerequisites Check

1. Check if `gh` is installed: `which gh`
2. Check if authenticated: `gh auth status`
3. Check API access: `gh api user --jq .login`

## Procedure

### Step 1 — Install gh CLI

If `gh` not found:
- macOS: `brew install gh`
- Linux: see https://github.com/cli/cli/blob/trunk/docs/install_linux.md
- Verify: `gh --version`

### Step 2 — Authenticate

If not authenticated:
1. Ask user to run: `! gh auth login`
   - Choose: GitHub.com
   - Choose: HTTPS protocol
   - Authenticate via browser or token
2. Verify: `gh auth status`

### Step 3 — Verify Repository Access

1. Check remote: `git remote -v` (should show github.com origin)
2. Test API: `gh api repos/{owner}/{repo} --jq .full_name`
3. Test push permissions: `gh api repos/{owner}/{repo} --jq .permissions.push`

### Step 4 — Configure Defaults

1. Set default repo: `gh repo set-default`
2. Confirm: `gh repo view --json nameWithOwner --jq .nameWithOwner`

## Verification Checklist

- [ ] `gh --version` succeeds
- [ ] `gh auth status` shows authenticated
- [ ] `gh api user` returns user info
- [ ] `gh repo view` shows correct repository

## Error Handling

- If brew not available: provide manual install URL
- If auth fails: suggest `! gh auth login --web` for browser flow
- If no remote: guide user to `git remote add origin <url>`
