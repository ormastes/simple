#!/usr/bin/env bash
# Hook: PostToolUse (Edit|Write) — Warn if code is being replaced with comments
set -euo pipefail

INPUT=$(cat)
TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty')

if [[ "$TOOL_NAME" != "Edit" && "$TOOL_NAME" != "Write" ]]; then
  exit 0
fi

# For Edit tool, check old_string vs new_string
if [[ "$TOOL_NAME" == "Edit" ]]; then
  OLD=$(echo "$INPUT" | jq -r '.tool_input.old_string // empty')
  NEW=$(echo "$INPUT" | jq -r '.tool_input.new_string // empty')

  if [[ -z "$OLD" || -z "$NEW" ]]; then
    exit 0
  fi

  OLD_LINES=$(echo "$OLD" | wc -l)
  NEW_LINES=$(echo "$NEW" | wc -l)
  REMOVED=$((OLD_LINES - NEW_LINES))

  if [[ $REMOVED -gt 5 ]]; then
    # Count comment lines in new content (lines starting with // or #)
    COMMENT_LINES=$(echo "$NEW" | grep -cP '^\s*(//|#)' || true)

    if [[ $NEW_LINES -gt 0 ]]; then
      COMMENT_PCT=$((COMMENT_LINES * 100 / NEW_LINES))
      if [[ $COMMENT_PCT -gt 50 ]]; then
        echo "WARNING: $REMOVED lines removed, and ${COMMENT_PCT}% of new lines are comments."
        echo "This looks like code may have been replaced with comments/placeholders."
        echo "Per CLAUDE.md: NEVER convert TODO/FIXME to NOTE. Either implement or delete entirely."
      fi
    fi
  fi
fi

exit 0
