#!/usr/bin/env bash
# Hook: PreToolUse (Bash) — Block destructive ops on protected binaries and databases
set -euo pipefail

INPUT=$(cat)
TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty')

if [[ "$TOOL_NAME" != "Bash" ]]; then
  exit 0
fi

CMD=$(echo "$INPUT" | jq -r '.tool_input.command // empty')

# Protected path patterns
PROTECTED_PATTERNS=(
  'bin/release/simple'
  'simple_bootstrap'
  'simple_stage'
  '.sdn'
)

# Destructive commands
DESTRUCTIVE_OPS='(^|\s|&&|\|\||;)(rm|mv|truncate|cp)\s'

if echo "$CMD" | grep -qP "$DESTRUCTIVE_OPS"; then
  for pattern in "${PROTECTED_PATTERNS[@]}"; do
    if echo "$CMD" | grep -q "$pattern"; then
      echo "BLOCKED: Destructive operation on protected file matching '$pattern'"
      echo "Protected files: bin/release/simple*, simple_bootstrap, simple_stage*, *.sdn"
      echo "If you need to modify these, ask the user for explicit approval."
      exit 2
    fi
  done
fi

exit 0
