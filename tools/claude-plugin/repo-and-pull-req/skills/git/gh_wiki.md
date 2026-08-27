# GitHub Wiki Skill

Auto-generate GitHub wiki pages from PR changes for knowledge sharing.

## Prerequisites

- `gh` CLI authenticated
- Active PR exists (from gh_push) — need PR number
- Wiki enabled on the repository (Settings → Features → Wikis)

## Procedure

### Step 1 — Gather Content

```bash
# PR metadata
PR_JSON=$(gh pr view "${PR_NUMBER}" --json title,body,files,commits,url)
PR_TITLE=$(echo "$PR_JSON" | jq -r .title)
PR_URL=$(echo "$PR_JSON" | jq -r .url)
PR_FILES=$(echo "$PR_JSON" | jq -r '.files[].path')

# Diff summary
DIFF_STAT=$(jj diff --stat -r @-)

# Commit messages
COMMIT_LOG=$(jj log -r @- --no-graph -T '"- " ++ description ++ "\n"')

# .sstack state (if exists)
SSTACK_STATE=""
if ls .sstack/*/state.md 1>/dev/null 2>&1; then
  SSTACK_STATE=$(cat .sstack/*/state.md | head -100)
fi
```

### Step 2 — Generate Wiki Page

Create a markdown page with this template:

```markdown
# PR #<number>: <title>

**PR:** <url> | **Date:** <date> | **Author:** <user>

## Summary

<From PR body / commit messages>

## Files Changed

| File | Status |
|------|--------|
<For each file: path and added/modified/deleted>

## Architecture Notes

<From .sstack state if available, or from commit messages mentioning
design decisions, new patterns, or breaking changes>

## Related

- PR: <url>
- Jira: <issue-key if linked>
- Previous: <links to related wiki pages if any>
```

### Step 3 — Push to Wiki

**Option A — via gh API** (preferred if wiki API available):

```bash
# GitHub wiki pages can be managed via the wiki git repo
REPO=$(gh repo view --json nameWithOwner --jq .nameWithOwner)
WIKI_DIR="/tmp/wiki-${PR_NUMBER}"

# Clone wiki repo
git clone "https://github.com/${REPO}.wiki.git" "${WIKI_DIR}" 2>/dev/null

# Write page
PAGE_NAME="PR-${PR_NUMBER}-$(echo "${PR_TITLE}" | tr ' ' '-' | tr -cd '[:alnum:]-' | head -c 40)"
cat > "${WIKI_DIR}/${PAGE_NAME}.md" <<EOF
${GENERATED_CONTENT}
EOF

# Commit and push
cd "${WIKI_DIR}"
git add "${PAGE_NAME}.md"
git commit -m "Add wiki page for PR #${PR_NUMBER}"
git push
cd -

# Cleanup
rm -rf "${WIKI_DIR}"
```

**Option B — manual** (if wiki not cloneable):

Print the generated content and ask user to paste it into the wiki UI.

### Step 4 — Link Wiki to PR

```bash
# Add wiki link to PR description
WIKI_URL="https://github.com/${REPO}/wiki/${PAGE_NAME}"
EXISTING_BODY=$(gh pr view "${PR_NUMBER}" --json body --jq .body)
gh pr edit "${PR_NUMBER}" --body "${EXISTING_BODY}\n\nWiki: ${WIKI_URL}"
```

## Page Naming Convention

`PR-<number>-<slug>.md` (e.g., `PR-42-add-csv-export.md`)

## Error Handling

- If wiki not enabled: warn user, print content to terminal instead
- If clone fails (wiki empty): `git init` + first commit
- If push fails: print content for manual paste
