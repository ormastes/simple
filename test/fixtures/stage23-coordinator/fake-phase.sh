#!/bin/sh
set -eu
phase=
transaction=
capsule=
stage=
run_id=
architecture=
reason=
mode=fresh
for arg in "$@"; do
    case "$arg" in
        --coordinator-phase=*) phase=${arg#*=} ;;
        --transaction-root=*) transaction=${arg#*=} ;;
        --capsule-root=*) capsule=${arg#*=} ;;
        --stage-root=*) stage=${arg#*=} ;;
        --run-id=*) run_id=${arg#*=} ;;
        --architecture=*) architecture=${arg#*=} ;;
        --reason=*) reason=${arg#*=} ;;
        --resume=*) mode=resume ;;
    esac
done
[ "${STAGE23_FIXTURE_FAIL_PHASE:-}" != "$phase" ] || exit 71
hash=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
case "$phase" in
    stage2)
        [ -n "$transaction" ]
        mkdir "$transaction"
        cat >"$transaction/coordinator-stage2.env" <<EOF
schema=simple-stage23-stage2-boundary-v1
status=pass
mode=$mode
run_id=${STAGE23_FIXTURE_RUN_ID:?}
architecture=${STAGE23_FIXTURE_ARCH:?}
artifact_sha256=$hash
EOF
        ;;
    planner)
        [ -n "$capsule" ]
        cat >"$capsule/coordinator-planner.env" <<EOF
schema=simple-stage23-planner-boundary-v1
status=pass
run_id=${STAGE23_FIXTURE_RUN_ID:?}
architecture=${STAGE23_FIXTURE_ARCH:?}
target=//bootstrap:stage3
reason=$reason
receipt_sha256=$hash
EOF
        ;;
    stage3)
        [ -n "$stage" ]
        cat >"$stage/coordinator-stage3.env" <<EOF
schema=simple-stage23-stage3-boundary-v1
status=pass
run_id=$run_id
architecture=$architecture
planner_receipt_sha256=$hash
terminal_sha256=$hash
runner_sha256=$hash
provenance_sha256=$hash
candidate_sha256=$hash
all_units_inactive=true
all_cgroups_empty=true
cleanup_complete=true
EOF
        ;;
    *) exit 64 ;;
esac
