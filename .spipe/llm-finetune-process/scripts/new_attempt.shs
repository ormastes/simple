#!/bin/sh
set -eu

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
HOST_ROOT="$(CDPATH= cd -- "${ROOT}/../.." && pwd)"
ATTEMPTS_DIR="${ROOT}/attempts"
TEMPLATE="${ATTEMPTS_DIR}/template.sdn"

usage() {
  cat <<'USAGE'
Usage: new_attempt.sh <attempt_id> <goal> [app_or_server_target]

Creates .spipe/llm-finetune-process/attempts/<attempt_id>.sdn from the
record template. The file is intentionally incomplete until research, model
choice, tuning method, training script, eval, and retry decision are filled.
USAGE
}

case "${1:-}" in
  ""|--help|-h) usage; exit 2 ;;
esac

ATTEMPT_ID="$1"
GOAL="${2:-}"
TARGET="${3:-}"

if [ -z "$GOAL" ]; then
  echo "new_attempt: goal is required" >&2
  usage >&2
  exit 2
fi

SPIPE_CLI="${HOST_ROOT}/.spipe/spipe_project/cli/spipe.js"
if [ -f "$SPIPE_CLI" ] && command -v node >/dev/null 2>&1; then
  cd "$HOST_ROOT"
  exec node "$SPIPE_CLI" fine-tune-new-attempt "$ATTEMPT_ID" "$GOAL" "$TARGET"
fi

case "$ATTEMPT_ID" in
  *[!A-Za-z0-9_.-]*)
    echo "new_attempt: attempt_id may contain only letters, numbers, dot, dash, and underscore" >&2
    exit 2
    ;;
esac

OUT="${ATTEMPTS_DIR}/${ATTEMPT_ID}.sdn"
if [ -e "$OUT" ]; then
  echo "new_attempt: attempt already exists: $OUT" >&2
  exit 1
fi

if [ ! -f "$TEMPLATE" ]; then
  echo "new_attempt: missing template: $TEMPLATE" >&2
  exit 1
fi

escape_sed() {
  printf '%s' "$1" | sed 's/[\/&]/\\&/g'
}

GOAL_ESC="$(escape_sed "$GOAL")"
TARGET_ESC="$(escape_sed "$TARGET")"

sed \
  -e "s/  attempt_id: \"\"/  attempt_id: \"${ATTEMPT_ID}\"/" \
  -e "s/  goal: \"\"/  goal: \"${GOAL_ESC}\"/" \
  -e "s/  app_or_server_target: \"\"/  app_or_server_target: \"${TARGET_ESC}\"/" \
  "$TEMPLATE" > "$OUT"

echo "$OUT"
