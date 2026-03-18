#!/usr/bin/env bash
# Hook: PostToolUse (Edit|Write) — Remind to lint .spl/.shs files
set -euo pipefail

INPUT=$(cat)
TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty')

if [[ "$TOOL_NAME" != "Edit" && "$TOOL_NAME" != "Write" ]]; then
  exit 0
fi

FILE_PATH=$(echo "$INPUT" | jq -r '.tool_input.file_path // empty')

if [[ "$FILE_PATH" == *.spl || "$FILE_PATH" == *.shs ]]; then
  echo "Reminder: Run 'bin/simple build lint' to check for style issues in modified .spl/.shs files."
fi

exit 0
