# Bug Fix Skill

For a specific bug: analyze code, identify root cause, propose and apply a fix.

## Prerequisites

- `bin/bug` configured
- Bug ID known (from `bin/bug list` or `/bug_review triage`)

## Procedure

### Step 1 — Fetch Bug Details

```bash
bin/bug fix <id>
# Outputs: bug details + file references + fix context
```

### Step 2 — Analyze Root Cause

1. Read each referenced file
2. Search for error messages or patterns mentioned in the bug
3. Check recent git history for related changes: `jj log --revisions .. <file>`
4. Identify the specific code path causing the issue

### Step 3 — Propose Fix

Based on analysis:
1. Describe the root cause
2. Propose the minimal code change that fixes the issue
3. Consider edge cases and side effects

### Step 4 — Apply Fix

Using the Edit tool:
1. Apply the proposed code changes
2. Verify no syntax errors
3. Run related tests if available: `bin/simple test <related-test-file>`

### Step 5 — Commit

```bash
jj commit -m "fix: <bug summary> (#<id>)"
```

### Step 6 — Report

Summarize:
- Bug: `<id>` — `<title>`
- Root cause: `<description>`
- Fix: `<files changed>`
- Tests: `<pass/fail>`

Suggest: run `/repo_and_pull_req push` to create a PR for the fix.

## Safety

- Never apply a fix without understanding the root cause
- If the bug is unclear or the fix is risky, ask the user before applying
- Run tests after fixing to catch regressions
