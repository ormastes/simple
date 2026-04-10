# Confluence Wiki Skill

Create/update Confluence pages with knowledge sharing for PRs.

## Prerequisites

- Atlassian API token configured (from jira_setup)
- Confluence space exists (same Atlassian workspace)
- Credentials from `~/.config/.jira/.config.yml`

## Procedure

### Step 1 — Read Credentials

```bash
# Extract from jira-cli config
JIRA_CONFIG="$HOME/.config/.jira/.config.yml"
SERVER=$(grep 'server:' "$JIRA_CONFIG" | awk '{print $2}' | sed 's|/$||')
EMAIL=$(grep 'login:' "$JIRA_CONFIG" | awk '{print $2}')
# API token: prompt user or read from keyring
# Ask user: "Enter your Atlassian API token (same as jira-cli):"
```

### Step 2 — Gather Content

Same as gh_wiki — PR metadata, diff stats, commit messages, .sstack state.

### Step 3 — Check for Existing Page

```bash
# Search for existing page with this PR title
SEARCH_RESULT=$(curl -s -u "${EMAIL}:${TOKEN}" \
  "${SERVER}/wiki/rest/api/content?title=PR+${PR_NUMBER}&spaceKey=${SPACE_KEY}" \
  -H "Accept: application/json")

PAGE_EXISTS=$(echo "$SEARCH_RESULT" | jq '.results | length > 0')
```

### Step 4 — Generate Confluence Content

Convert markdown to Confluence storage format (XHTML subset):

```xml
<h1>PR #<number>: <title></h1>
<ac:structured-macro ac:name="info">
  <ac:rich-text-body>
    <p><strong>PR:</strong> <a href="<url>">#<number></a> |
       <strong>Date:</strong> <date> |
       <strong>Status:</strong> <status></p>
  </ac:rich-text-body>
</ac:structured-macro>

<h2>Summary</h2>
<p><description></p>

<h2>Files Changed</h2>
<table>
  <tr><th>File</th><th>Status</th></tr>
  <tr><td><file></td><td><status></td></tr>
</table>

<h2>Architecture Notes</h2>
<p><decisions></p>
```

### Step 5a — Create New Page

```bash
curl -s -u "${EMAIL}:${TOKEN}" \
  -X POST "${SERVER}/wiki/rest/api/content" \
  -H "Content-Type: application/json" \
  -d '{
    "type": "page",
    "title": "PR #'"${PR_NUMBER}"': '"${PR_TITLE}"'",
    "space": {"key": "'"${SPACE_KEY}"'"},
    "body": {
      "storage": {
        "value": "'"${CONTENT}"'",
        "representation": "storage"
      }
    }
  }'
```

### Step 5b — Update Existing Page

```bash
# Get current version
PAGE_ID=$(echo "$SEARCH_RESULT" | jq -r '.results[0].id')
CURRENT_VERSION=$(echo "$SEARCH_RESULT" | jq -r '.results[0].version.number')
NEXT_VERSION=$((CURRENT_VERSION + 1))

curl -s -u "${EMAIL}:${TOKEN}" \
  -X PUT "${SERVER}/wiki/rest/api/content/${PAGE_ID}" \
  -H "Content-Type: application/json" \
  -d '{
    "version": {"number": '"${NEXT_VERSION}"'},
    "title": "PR #'"${PR_NUMBER}"': '"${PR_TITLE}"'",
    "type": "page",
    "body": {
      "storage": {
        "value": "'"${CONTENT}"'",
        "representation": "storage"
      }
    }
  }'
```

### Step 6 — Link to PR and Jira

```bash
# Get page URL from response
PAGE_URL="${SERVER}/wiki/spaces/${SPACE_KEY}/pages/${PAGE_ID}"

# Add to PR description
gh pr edit "${PR_NUMBER}" --body "${EXISTING_BODY}\n\nConfluence: ${PAGE_URL}"

# Add to Jira issue (if linked)
if [ -n "${ISSUE_KEY}" ]; then
  jira issue comment add "${ISSUE_KEY}" --body "Confluence: ${PAGE_URL}"
fi
```

## Configuration

First-time use: ask user for Confluence space key and store it.
The API token is the same one used for jira-cli.

## Error Handling

- If Confluence not accessible (404/403): warn user, skip wiki (non-fatal)
- If page exists with same title: update instead of create (Step 5b)
- If API returns 401: redirect to `/repo_and_pull_req setup jira`
- If no SPACE_KEY configured: ask user to provide it
