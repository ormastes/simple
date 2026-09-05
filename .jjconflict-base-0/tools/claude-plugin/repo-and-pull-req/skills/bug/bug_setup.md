# Bug Tracking Setup Skill

Setup unified bug tracking via `bin/bug` CLI (GitHub Issues + Jira).

## Prerequisites Check

1. `bin/bug version` — CLI available
2. `gh auth status` — GitHub authenticated
3. `bin/jira auth status` — Jira authenticated (optional)

## Procedure

### Step 1 — Verify CLI

```bash
bin/bug version
# Expected: bug-cli version 0.1.0
```

### Step 2 — Initialize Config

```bash
bin/bug config init
# Creates ~/.config/bug-cli/config.json with defaults
```

### Step 3 — Enable Sources

GitHub (enabled by default if `gh` is authenticated):
```bash
bin/bug config set github_enabled true
```

Jira (enable if `bin/jira auth status` succeeds):
```bash
bin/bug config set jira_enabled true
```

### Step 4 — Verify

```bash
bin/bug list --limit 5
# Should show bugs from enabled sources
```

## Verification Checklist

- [ ] `bin/bug version` shows both source availability
- [ ] `bin/bug list` returns results
- [ ] `~/.config/bug-cli/config.json` exists
