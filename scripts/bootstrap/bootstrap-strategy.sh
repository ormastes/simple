#!/bin/sh
# Supervise canonical bootstrap plus immutable, isolated per-phase verification.
# The canonical child remains the only writer of bootstrap caches/artifacts.

set -u

die() {
  echo "bootstrap-strategy: $*" >&2
  exit 2
}

value() {
  key=$1
  file=$2
  sed -n "s/^${key}=//p" "$file" | head -n 1
}

hash_file() {
  sha256sum "$1" | awk '{print $1}'
}

strategy=${SIMPLE_BOOTSTRAP_STRATEGY:-normal}
output=build/bootstrap
platform=""
child_script=scripts/bootstrap/bootstrap-from-scratch.sh
runner=scripts/bootstrap/bootstrap-phase-verification.shs
evidence_root=""
poll_seconds=${BOOTSTRAP_STRATEGY_POLL_SECONDS:-2}
memory_floor_mib=${BOOTSTRAP_VERIFY_MEMORY_FLOOR_MIB:-4096}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --strategy=*) strategy=${1#*=}; shift ;;
    --output=*) output=${1#*=}; shift ;;
    --platform=*) platform=${1#*=}; shift ;;
    --child-script=*) child_script=${1#*=}; shift ;;
    --verification-runner=*) runner=${1#*=}; shift ;;
    --evidence-root=*) evidence_root=${1#*=}; shift ;;
    --poll-seconds=*) poll_seconds=${1#*=}; shift ;;
    --memory-floor-mib=*) memory_floor_mib=${1#*=}; shift ;;
    --) shift; break ;;
    *) die "unknown supervisor option before --: $1" ;;
  esac
done

case "$strategy" in adhoc|normal|full) ;; *) die "strategy must be adhoc, normal, or full" ;; esac
case "$poll_seconds" in ''|*[!0-9]*|0) die "poll interval must be positive" ;; esac
case "$memory_floor_mib" in ''|*[!0-9]*) die "memory floor must be numeric" ;; esac
[ -x "$child_script" ] || die "canonical child is not executable: $child_script"
if [ "$strategy" != adhoc ]; then
  [ -x "$runner" ] || die "phase verifier is not executable: $runner"
fi

mkdir -p "$output"
output=$(cd "$output" && pwd -P)
if [ -z "$evidence_root" ]; then
  run_id=$(date -u +%Y%m%dT%H%M%SZ)-$$
  evidence_root="$output/strategy-$strategy/$run_id"
fi
mkdir -p "$evidence_root"
evidence_root=$(cd "$evidence_root" && pwd -P)
lock_dir="$evidence_root/.supervisor-lock"
mkdir "$lock_dir" 2>/dev/null || die "strategy evidence lane is already active: $evidence_root"
child_pid=""
verify_pid=""
cleanup() {
  [ -z "$verify_pid" ] || kill "$verify_pid" 2>/dev/null || :
  [ -z "$child_pid" ] || kill "$child_pid" 2>/dev/null || :
  rmdir "$lock_dir" 2>/dev/null || :
}
trap cleanup EXIT
trap 'exit 130' INT TERM HUP
source_root=$(pwd -P)
summary="$evidence_root/terminal-summary.env"
child_log="$evidence_root/canonical-bootstrap.log"
: >"$summary"
{
  echo "schema=bootstrap-strategy-summary-v1"
  echo "strategy=$strategy"
  echo "phase_verification=$([ "$strategy" = adhoc ] && echo disabled || echo inventory-to-end)"
  echo "verification_cache=$([ "$strategy" = adhoc ] && echo disabled || echo incremental-isolated)"
  echo "canonical_hash_policy=fail"
  echo "temporary_diagnostic_hash_policy=warning-only"
} >>"$summary"

env SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1 \
  "$child_script" --strategy="$strategy" --output="$output" "$@" >"$child_log" 2>&1 &
child_pid=$!
child_done=0
child_status=0

if [ "$strategy" = adhoc ]; then
  wait "$child_pid" || child_status=$?
  child_pid=""
  echo "canonical_bootstrap_status=$child_status" >>"$summary"
  echo "canonical_bootstrap_result=$([ "$child_status" -eq 0 ] && echo PASS || echo FAIL)" >>"$summary"
  echo "overall=$([ "$child_status" -eq 0 ] && echo PASS || echo FAIL)" >>"$summary"
  exit "$child_status"
fi

phase2_state=pending
phase3_state=pending
verify_phase=""
phase2_reason=not-admitted
phase3_reason=not-admitted

memory_allows_verification() {
  [ "$memory_floor_mib" -eq 0 ] && return 0
  [ -r /proc/meminfo ] || return 0
  available_kib=$(sed -n 's/^MemAvailable:[[:space:]]*\([0-9][0-9]*\).*/\1/p' /proc/meminfo)
  [ -n "$available_kib" ] || return 0
  [ "$available_kib" -ge "$((memory_floor_mib * 1024))" ]
}

discover_platform() {
  [ -n "$platform" ] && return 0
  for candidate in "$output"/stage3/*; do
    [ -d "$candidate" ] || continue
    platform=$(basename "$candidate")
    return 0
  done
  return 1
}

phase_admission() {
  requested=$1
  PHASE_REASON=not-admitted
  discover_platform || return 1
  base="$output/stage3/$platform"
  case "$requested" in
    stage2)
      admitted="$base/stage2-admitted/simple"
      receipt="$base/stage2-sanity.env"
      [ -x "$admitted" ] && [ -f "$receipt" ] || return 1
      [ "$(value status "$receipt")" = pass ] || { PHASE_REASON=receipt-rejected; return 1; }
      admitted_sha=$(value candidate_sha256_after "$receipt")
      ;;
    stage3)
      admitted="$base/simple"
      receipt="$base/provenance.env"
      [ -x "$admitted" ] && [ -f "$receipt" ] || return 1
      [ "$(value status "$receipt")" = pass ] || { PHASE_REASON=receipt-rejected; return 1; }
      admitted_sha=$(value stage3_sha256 "$receipt")
      ;;
    *) return 1 ;;
  esac
  [ -n "$admitted_sha" ] || { PHASE_REASON=receipt-missing-hash; return 1; }
  [ "$(hash_file "$admitted")" = "$admitted_sha" ] || { PHASE_REASON=canonical-hash-mismatch; return 1; }
  PHASE_COMPILER=$admitted
  PHASE_SHA=$admitted_sha
  PHASE_REASON=admitted
}

start_verification() {
  requested=$1
  compiler=$2
  sha=$3
  phase_work="$evidence_root/$requested"
  phase_cache="$output/phase-verification-cache/$requested/$sha"
  "$runner" --phase="$requested" --compiler="$compiler" \
    --compiler-sha256="$sha" --strategy="$strategy" --hash-policy=canonical \
    --work-root="$phase_work" --cache-root="$phase_cache" \
    --source-root="$source_root" >"$phase_work.runner.log" 2>&1 &
  verify_pid=$!
  verify_phase=$requested
  eval "${requested}_state=running"
}

reap_verification() {
  [ -n "$verify_pid" ] || return 0
  kill -0 "$verify_pid" 2>/dev/null && return 0
  status=0
  wait "$verify_pid" || status=$?
  eval "${verify_phase}_state=done"
  echo "${verify_phase}_verification_status=$status" >>"$summary"
  verify_pid=""
  verify_phase=""
}

while :; do
  if [ "$child_done" -eq 0 ] && ! kill -0 "$child_pid" 2>/dev/null; then
    wait "$child_pid" || child_status=$?
    child_pid=""
    child_done=1
    echo "canonical_bootstrap_status=$child_status" >>"$summary"
    child_result=PASS
    case "$child_status" in
      0) child_result=PASS ;;
      124|137) child_result=TIMEOUT ;;
      134|136|139) child_result=CRASH ;;
      *) child_result=FAIL ;;
    esac
    echo "canonical_bootstrap_result=$child_result" >>"$summary"
  fi

  reap_verification

  if [ -z "$verify_pid" ] && { memory_allows_verification || [ "$child_done" -eq 1 ]; }; then
    if [ "$phase2_state" = pending ]; then
      if phase_admission stage2; then
        start_verification stage2 "$PHASE_COMPILER" "$PHASE_SHA"
      else
        phase2_reason=$PHASE_REASON
      fi
    elif [ "$phase3_state" = pending ]; then
      if phase_admission stage3; then
        start_verification stage3 "$PHASE_COMPILER" "$PHASE_SHA"
      else
        phase3_reason=$PHASE_REASON
      fi
    fi
  fi

  if [ "$child_done" -eq 1 ] && [ -z "$verify_pid" ]; then
    # One final discovery occurs after the child terminalizes. Missing phases
    # become explicit blocked descendants instead of disappearing from output.
    launched=0
    if [ "$phase2_state" = pending ]; then
      if phase_admission stage2; then
        start_verification stage2 "$PHASE_COMPILER" "$PHASE_SHA"; launched=1
      else
        phase2_reason=$PHASE_REASON
      fi
    elif [ "$phase3_state" = pending ]; then
      if phase_admission stage3; then
        start_verification stage3 "$PHASE_COMPILER" "$PHASE_SHA"; launched=1
      else
        phase3_reason=$PHASE_REASON
      fi
    fi
    [ "$launched" -eq 1 ] || break
  fi
  sleep "$poll_seconds"
done

[ "$phase2_state" = done ] || echo "stage2_verification_status=BLOCKED:$phase2_reason" >>"$summary"
[ "$phase3_state" = done ] || echo "stage3_verification_status=BLOCKED:$phase3_reason" >>"$summary"
echo "stage1_verification_status=SKIPPED:bootstrap-seed-only" >>"$summary"
echo "stage4_verification_status=BLOCKED:tools-only-producer-unavailable" >>"$summary"

overall=PASS
[ "$child_status" -eq 0 ] || overall=FAIL
grep -qE '_verification_status=([1-9][0-9]*|BLOCKED)' "$summary" && overall=FAIL
echo "overall=$overall" >>"$summary"
[ "$overall" = PASS ]
