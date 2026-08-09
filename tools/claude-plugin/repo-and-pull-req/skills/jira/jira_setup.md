# Jira CLI Setup Skill

Interactive setup for our custom Jira CLI (`tools/jira-cli`) — a gh-like interface for Atlassian Cloud.

## Prerequisites Check

1. Check if jira-cli available: `bin/jira version`
2. Check if configured: `bin/jira auth status`
3. Check config: `~/.config/jira-cli/config.json`

## Procedure

### Step 1 — Verify jira-cli

The tool lives at `tools/jira-cli/bin/jira` with a symlink at `bin/jira`.
```bash
bin/jira version
# Expected: jira-cli version 0.1.0 (Simple Language Project)
```

If symlink missing: `ln -sf ../tools/jira-cli/bin/jira bin/jira`

Dependencies: `curl`, `jq` (install via `brew install curl jq` if missing).

### Step 2 — Create Atlassian Account (if needed)

If user has no Atlassian account:
1. Guide to: https://www.atlassian.com/software/jira/free (free tier, up to 10 users)
2. Sign up with email (e.g., ormastes@gmail.com)
3. Create a workspace (e.g., `ormastes.atlassian.net`)
4. Create a default project (e.g., key: SIMPLE, type: Scrum/Kanban)

### Step 3 — Get API Token

1. Guide to: https://id.atlassian.com/manage-profile/security/api-tokens
2. Click "Create API token"
3. Label: `claude-code-jira`
4. Copy token (shown only once)

### Step 4 — Configure jira-cli

Ask user to run interactively: `! bin/jira auth login`

The login flow will prompt for:
- Server URL: `https://<workspace>.atlassian.net`
- Email: `ormastes@gmail.com`
- API token: (paste from Step 3)
- Default project key: (e.g., SIMPLE)
- Default Confluence space key: (e.g., SIMPLE)

Credentials are verified against `/rest/api/3/myself` during login.
Config stored at: `~/.config/jira-cli/config.json` (mode 600).

### Step 5 — Verify Access

```bash
bin/jira auth status     # Shows auth status + token health check
bin/jira me              # Shows current user info
bin/jira project list    # Lists accessible projects
bin/jira issue list      # Lists issues in default project
bin/jira wiki space list # Lists Confluence spaces
```

## Verification Checklist

- [ ] `bin/jira version` succeeds
- [ ] `bin/jira auth status` shows "Logged in" with valid token
- [ ] `bin/jira me` shows user info
- [ ] `bin/jira project list` returns projects
- [ ] `~/.config/jira-cli/config.json` exists

## Command Reference (mirrors gh)

| gh command | jira equivalent |
|------------|----------------|
| `gh auth login` | `jira auth login` |
| `gh auth status` | `jira auth status` |
| `gh issue list` | `jira issue list` |
| `gh issue create` | `jira issue create` |
| `gh issue view #N` | `jira issue view PROJ-123` |
| `gh issue comment #N` | `jira issue comment PROJ-123` |
| `gh api <endpoint>` | `jira api <endpoint>` |
| N/A | `jira wiki create` |
| N/A | `jira wiki list` |

## Error Handling

- If `curl` or `jq` not found: `brew install curl jq`
- If auth fails (HTTP 401): verify API token, re-run `! bin/jira auth login`
- If no project: create one at `https://<workspace>.atlassian.net`
- If token expired: regenerate at https://id.atlassian.com/manage-profile/security/api-tokens
