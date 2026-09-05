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
    agents/review_loop_codex_first.md \
    agents/bug_triage.md; do
    if [ ! -f "${SCRIPT_DIR}/${f}" ]; then
        echo "ERROR: Referenced file ${f} not found"; exit 1
    fi
    echo "  OK: ${f}"
done

# Keep the L2 exact-head admission contract synchronized across the public
# skill and both review agents. Same-author automation must never regress to a
# provider self-approval/retry loop.
for f in \
    skills/git/gh_pull_req_review.md \
    agents/review_loop.md \
    agents/review_loop_codex_first.md; do
    grep -q 'SPipe Self Review Admission' "${SCRIPT_DIR}/${f}" || {
        echo "ERROR: ${f} is missing scoped self-review admission"; exit 1;
    }
done
if grep -Eq '[Ww]ait(s|ing)? for human|HUMAN_APPROVED' \
    "${SCRIPT_DIR}/skills/git/gh_pull_req_review.md" \
    "${SCRIPT_DIR}/agents/review_loop.md" \
    "${SCRIPT_DIR}/agents/review_loop_codex_first.md"; then
    echo "ERROR: provider User-account approval must not be claimed as guaranteed human approval"
    exit 1
fi
echo "OK: review admission and provider-account wording are synchronized"

# A clean PR must still reach L2/L3 admission, and persisted approval/evidence
# state must remain exact-head and fail closed.
if grep -Fq 'If no pending reviews and no unresolved comments: exit' \
    "${SCRIPT_DIR}/skills/git/gh_pull_req_review.md"; then
    echo "ERROR: clean PR exits before L2/L3 admission"; exit 1
fi
if ! awk '
    /^### Step 1 / { in_step1=1; next }
    /^### Step 2 / { in_step1=0 }
    in_step1 && /^REPO=\$\(gh repo view / { found=1 }
    END { exit(found ? 0 : 1) }
' "${SCRIPT_DIR}/skills/git/gh_pull_req_review.md"; then
    echo "ERROR: shared Step 1 does not initialize REPO for a clean L2/L3 PR"; exit 1
fi
if ! awk '
    /^#### L3 / { in_l3=1; next }
    /^### Step 5b / { in_l3=0 }
    in_l3 && /repos\/\$\{REPO\}\/pulls\/\$\{PR_NUMBER\}/ { found=1 }
    END { exit(found ? 0 : 1) }
' "${SCRIPT_DIR}/skills/git/gh_pull_req_review.md"; then
    echo "ERROR: clean L3 provider lookup is not bound to initialized REPO"; exit 1
fi
grep -Fq 'USER_ACCOUNT_APPROVED=false' "${SCRIPT_DIR}/agents/review_loop.md" || {
    echo "ERROR: provider approval is not reset before revalidation"; exit 1;
}
for field in review_head_sha reviewer_model reviewer_effort review_p0_count review_p1_count; do
    grep -Fq "$field" "${SCRIPT_DIR}/agents/review_loop.md" || {
        echo "ERROR: review state is missing $field"; exit 1;
    }
done
echo "OK: clean-PR flow and exact reviewer state are synchronized"

# Validate JSON syntax
if python3 -c "import json, sys; json.load(open(sys.argv[1]))" \
    "${SCRIPT_DIR}/.claude-plugin/plugin.json" 2>/dev/null; then
    echo "OK: plugin.json is valid JSON"
else
    echo "ERROR: plugin.json is not valid JSON"; exit 1
fi

echo "=== repo-and-pull-req plugin validated ==="
