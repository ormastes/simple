#!/usr/bin/env bash
# Build script for repo-and-pull-req Claude plugin
# Validates manifest and referenced files.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "=== repo-and-pull-req plugin build ==="

# Validate plugin.json exists
if [ ! -f "${SCRIPT_DIR}/.claude-plugin/plugin.json" ]; then
    echo "ERROR: .claude-plugin/plugin.json not found"; exit 1
fi

# Validate all referenced files exist
for f in \
    skills/git/gh_setup.md \
    skills/git/gh_push.md \
    skills/git/gh_wiki.md \
    skills/git/gh_pull_req_review.md \
    skills/jira/jira_setup.md \
    skills/jira/jira_push.md \
    skills/jira/jira_wiki.md \
    skills/jira/jira_pull_req_review.md \
    skills/bug/bug_setup.md \
    skills/bug/bug_review.md \
    skills/bug/bug_fix.md \
    skills/mail/mail_setup.md \
    skills/mail/mail_send.md \
    skills/mail/mail_review.md \
    skills/mail/mail_notify.md \
    agents/review_loop.md \
    agents/bug_triage.md; do
    if [ ! -f "${SCRIPT_DIR}/${f}" ]; then
        echo "ERROR: Referenced file ${f} not found"; exit 1
    fi
    echo "  OK: ${f}"
done

# Validate JSON syntax
if python3 -c "import json, sys; json.load(open(sys.argv[1]))" \
    "${SCRIPT_DIR}/.claude-plugin/plugin.json" 2>/dev/null; then
    echo "OK: plugin.json is valid JSON"
else
    echo "ERROR: plugin.json is not valid JSON"; exit 1
fi

echo "=== repo-and-pull-req plugin validated ==="
