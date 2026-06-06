#!/bin/sh
set -eu

usage() {
  cat <<'USAGE'
Usage: verify_attempt.sh <attempt-record.sdn>

Checks that an LLM fine-tune attempt record contains evidence fields needed by
SPipe verification. This is a structural gate, not a model quality evaluator.
When the separated SPipe CLI is available, this script delegates to
`spipe fine-tune-verify`.
USAGE
}

case "${1:-}" in
  ""|--help|-h) usage; exit 2 ;;
esac

RECORD="$1"
if [ ! -f "$RECORD" ]; then
  echo "ERROR missing_record $RECORD" >&2
  exit 1
fi

HOST_ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/../../.." && pwd)"
SPIPE_CLI="${HOST_ROOT}/.spipe/spipe_project/cli/spipe.js"
if [ -f "$SPIPE_CLI" ] && command -v node >/dev/null 2>&1; then
  exec node "$SPIPE_CLI" fine-tune-verify "$RECORD"
fi

value_for() {
  key="$1"
  sed -n "s/^[[:space:]]*${key}: \"\\(.*\\)\"[[:space:]]*$/\\1/p" "$RECORD" | tail -1
}

require_nonempty() {
  key="$1"
  val="$(value_for "$key")"
  if [ -z "$val" ]; then
    echo "ERROR missing_field $key"
    return 1
  fi
  return 0
}

status=0

for key in \
  attempt_id \
  goal \
  research_doc \
  feature_option \
  nfr_option \
  selection_doc \
  requirements_doc \
  nfr_doc \
  plan_doc \
  architecture_doc \
  design_doc \
  candidate_model \
  base_model \
  base_model_reason \
  download_command \
  cache_path \
  method \
  training_script \
  training_command \
  model_artifact \
  eval_command \
  metrics \
  target \
  result \
  status \
  app_target \
  handoff_doc
do
  require_nonempty "$key" || status=1
done

decision="$(value_for status)"
retry_target="$(value_for retry_target)"
case "$decision" in
  accepted)
    ;;
  retry-implementation|retry-data-research|retry-base-model|retry-tuning-method|try-other-way)
    if [ -z "$retry_target" ]; then
      echo "ERROR missing_field retry_target"
      status=1
    fi
    ;;
  "")
    ;;
  *)
    echo "ERROR invalid_status $decision"
    status=1
    ;;
esac

training_script="$(value_for training_script)"
if [ -n "$training_script" ] && [ "$training_script" != "provider-managed" ]; then
  case "$training_script" in
    /*) script_path="$training_script" ;;
    *) script_path="$(CDPATH= cd -- "$(dirname -- "$RECORD")/../../.." && pwd)/$training_script" ;;
  esac
  if [ ! -f "$script_path" ]; then
    echo "ERROR missing_training_script $training_script"
    status=1
  fi
fi

if [ "$status" -eq 0 ]; then
  echo "STATUS: PASS llm-finetune-attempt-record"
else
  echo "STATUS: FAIL llm-finetune-attempt-record"
fi

exit "$status"
