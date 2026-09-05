# Bug Review Skill

AI-powered bug review: fetch open bugs, analyze patterns, prioritize, suggest fix approaches.

## Prerequisites

- `bin/bug` configured (run `/bug_review setup` if not)

## Procedure

### Step 1 — Fetch and Triage

```bash
bin/bug triage --limit 50
```

This auto-classifies bugs by severity (critical/high/medium/low) and component.

### Step 2 — Analyze Patterns

For the triaged bug list:
1. Group by component — are multiple bugs hitting the same area?
2. Check for common root causes (shared stack traces, same file references)
3. Identify regressions (bugs mentioning "worked before", "regression", recent dates)

### Step 3 — Read Related Code

For each high/critical bug:
1. Extract file paths from bug description
2. Read those files to understand the affected code
3. Check `jj log` for recent changes to those files

### Step 4 — Generate Report

Output a prioritized report:

```
## Bug Review Report — <date>

### Critical (N bugs)
- <id>: <title> — <suggested approach>

### High (N bugs)
- <id>: <title> — <suggested approach>

### Patterns Found
- <component>: N bugs — possible root cause: <analysis>

### Recommended Next Actions
1. Fix <id> first (blocks N other bugs)
2. Investigate <component> area (cluster of related bugs)
```

### Step 5 — Optionally Start Fixes

For each critical bug, offer to run `/bug_review fix <id>` to propose a code patch.

## Integration

- After fixes: use `/repo_and_pull_req push` to create PRs
- After triage: update labels via `gh issue edit` or `bin/jira issue move`
