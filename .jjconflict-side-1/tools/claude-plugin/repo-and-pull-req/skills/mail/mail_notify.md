# Mail Notify Skill

Send email notifications for PR events (new PR, review comments, merge).

## Prerequisites

- Email account configured (`bin/mail auth status`)
- Active PR (from `/repo_and_pull_req push`)

## Procedure

### Step 1 — Gather PR Context

```bash
PR_JSON=$(gh pr view ${PR_NUMBER} --json title,body,url,files,author,reviewRequests)
PR_TITLE=$(echo "$PR_JSON" | jq -r '.title')
PR_URL=$(echo "$PR_JSON" | jq -r '.url')
PR_AUTHOR=$(echo "$PR_JSON" | jq -r '.author.login')
PR_FILES=$(echo "$PR_JSON" | jq -r '.files[].path' | head -20)
```

### Step 2 — Generate Notification Email

Template:
```
Subject: [PR #${PR_NUMBER}] ${PR_TITLE}

A new pull request has been created:

  PR: ${PR_URL}
  Author: ${PR_AUTHOR}
  Title: ${PR_TITLE}

Files changed:
${PR_FILES}

Please review when you have a moment.
```

### Step 3 — Send Notification

```bash
bin/mail send \
  --to "<team-email>" \
  --subject "[PR #${PR_NUMBER}] ${PR_TITLE}" \
  --body "<generated body>"
```

### Event-Specific Templates

**New PR:**
Subject: `[PR #N] <title>`
Body: PR details + files changed

**Review Comment:**
Subject: `Re: [PR #N] <title> — new comment`
Body: Comment text + context

**PR Merged:**
Subject: `[PR #N] <title> — merged`
Body: Merge confirmation + stats

**PR Approved:**
Subject: `Re: [PR #N] <title> — approved`
Body: Approval + reviewer name

## Integration

- Called by `review_loop` agent after processing PR comments
- Called by `gh_push` skill after creating a new PR
