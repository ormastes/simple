# Jira CLI Setup Skill

Interactive setup for Jira CLI (`ankitpokhrel/jira-cli`) integration.

## Prerequisites Check

1. Check if jira-cli installed: `which jira`
2. Check if configured: `jira me`
3. Check config: `~/.config/.jira/.config.yml`

## Procedure

### Step 1 — Install jira-cli

If `jira` not found:
- macOS: `brew install ankitpokhrel/jira-cli/jira-cli`
- Go: `go install github.com/ankitpokhrel/jira-cli/cmd/jira@latest`
- Verify: `jira version`

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

Ask user to run: `! jira init`
- Installation type: Cloud
- Server: `https://<workspace>.atlassian.net`
- Login email: `ormastes@gmail.com`
- API token: (paste from Step 3)
- Default project: (user-specified)
- Default board: (user-specified, or skip)

Config stored at: `~/.config/.jira/.config.yml`

### Step 5 — Verify Access

1. `jira me` — shows user profile
2. `jira project list` — lists accessible projects
3. `jira sprint list --current` — shows current sprint (if Scrum)
4. `jira issue list` — lists issues

## Verification Checklist

- [ ] `jira version` succeeds
- [ ] `jira me` shows authenticated user
- [ ] `jira project list` returns projects
- [ ] `~/.config/.jira/.config.yml` exists

## Error Handling

- If brew not available: suggest `go install` path
- If auth fails: verify API token, re-run `! jira init`
- If no project: guide user to create one in Atlassian web UI
- If 401 error: token may have expired, regenerate at API tokens page
