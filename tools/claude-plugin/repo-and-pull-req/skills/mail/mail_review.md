# Mail Review Skill

Review inbox for PR-related notification emails, cross-reference with GitHub PRs.

## Prerequisites

- Email account configured (`bin/mail auth status`)
- `gh` CLI authenticated

## Procedure

### Step 1 — Search for PR Notifications

```bash
bin/mail search "pull request" --since "7-Apr-2026" --limit 20
```

Also search for:
```bash
bin/mail search "review requested" --since "7-Apr-2026"
bin/mail search "commented on" --since "7-Apr-2026"
bin/mail search "merged" --since "7-Apr-2026"
```

### Step 2 — Read Relevant Messages

For each notification:
```bash
bin/mail read <uid>
```

Extract:
- PR number and repository from email body
- Action: review requested / comment / approval / merge
- Who triggered the action

### Step 3 — Cross-Reference with GitHub

For each PR mentioned:
```bash
gh pr view <number> --json state,reviewDecision,reviews,comments
```

### Step 4 — Generate Summary

```
## Email Review Summary — <date>

### Action Required
- PR #42: Review requested by @user — needs your review
- PR #38: New comment from @reviewer — needs response

### Informational
- PR #40: Merged by @maintainer
- PR #35: Approved by @reviewer

### Unread PR Emails: N
```

### Step 5 — Mark Processed

After review, optionally archive processed notifications:
```bash
bin/mail archive <uid>
```
