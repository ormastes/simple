#!/bin/sh
set -eu

run_id=
manifest=
manifest_display=
manifest_root_display=
bound_artifacts_descriptor=
scratch_root=
root=
candidate=
candidate_display=
source_snapshot=
runtime_snapshot=
tool_snapshot=
git_receipt=
verifier_sha256=
facade=
facade_display=
bootstrap_script_descriptor=
candidate_frontend_descriptor=
authority_descriptor=
command_descriptor=
sanity_descriptor=
manifest_write_descriptor=
manifest_verify_descriptor=
self_test_descriptor=
runner_descriptor=
launch_plan=
launch_plan_sha256=
memory=
phase=
admitted_compiler=
admitted_compiler_display=
memory_display=
phase_display=
stage3_transcript_descriptor=
stage3_transcript_display=
helper_capsule_inventory=
helper_capsule_inventory_sha256=
helper_capsule_entry_parity_sha256=
stage2_parent_trust_root=0
stage2_admission=

for option in "$@"; do
    case "$option" in
        --run-id=*) run_id=${option#*=} ;;
        --manifest=*) manifest=${option#*=} ;;
        --manifest-display=*) manifest_display=${option#*=} ;;
        --manifest-root-display=*) manifest_root_display=${option#*=} ;;
        --bound-artifacts-descriptor=*)
            bound_artifacts_descriptor=${option#*=} ;;
        --scratch-root=*) scratch_root=${option#*=} ;;
        --root=*) root=${option#*=} ;;
        --candidate=*) candidate=${option#*=} ;;
        --candidate-display=*) candidate_display=${option#*=} ;;
        --source-snapshot=*) source_snapshot=${option#*=} ;;
        --runtime-snapshot=*) runtime_snapshot=${option#*=} ;;
        --tool-snapshot=*) tool_snapshot=${option#*=} ;;
        --git-receipt=*) git_receipt=${option#*=} ;;
        --verifier-sha256=*) verifier_sha256=${option#*=} ;;
        --facade=*) facade=${option#*=} ;;
        --facade-display=*) facade_display=${option#*=} ;;
        --bootstrap-script-descriptor=*)
            bootstrap_script_descriptor=${option#*=} ;;
        --candidate-frontend-descriptor=*)
            candidate_frontend_descriptor=${option#*=} ;;
        --authority-descriptor=*) authority_descriptor=${option#*=} ;;
        --command-descriptor=*) command_descriptor=${option#*=} ;;
        --sanity-descriptor=*) sanity_descriptor=${option#*=} ;;
        --manifest-write-descriptor=*) manifest_write_descriptor=${option#*=} ;;
        --manifest-verify-descriptor=*) manifest_verify_descriptor=${option#*=} ;;
        --self-test-descriptor=*) self_test_descriptor=${option#*=} ;;
        --runner-descriptor=*) runner_descriptor=${option#*=} ;;
        --launch-plan=*) launch_plan=${option#*=} ;;
        --launch-plan-sha256=*) launch_plan_sha256=${option#*=} ;;
        --memory=*) memory=${option#*=} ;;
        --memory-display=*) memory_display=${option#*=} ;;
        --phase=*) phase=${option#*=} ;;
        --phase-display=*) phase_display=${option#*=} ;;
        --admitted-compiler=*) admitted_compiler=${option#*=} ;;
        --admitted-compiler-display=*) admitted_compiler_display=${option#*=} ;;
        --stage3-transcript-descriptor=*)
            stage3_transcript_descriptor=${option#*=} ;;
        --stage3-transcript-display=*) stage3_transcript_display=${option#*=} ;;
        --helper-capsule-inventory=*) helper_capsule_inventory=${option#*=} ;;
        --helper-capsule-inventory-sha256=*)
            helper_capsule_inventory_sha256=${option#*=} ;;
        --helper-capsule-entry-parity-sha256=*)
            helper_capsule_entry_parity_sha256=${option#*=} ;;
        --stage2-parent-trust-root) stage2_parent_trust_root=1 ;;
        --stage2-admission=*) stage2_admission=${option#*=} ;;
        *) echo "stage3 provenance verifier: unknown option" >&2; exit 64 ;;
    esac
done

# A freshly bootstrapped Stage 2 trust root has not itself been produced by the
# Stage 3 command recorded by provenance-v4.  Do not fabricate that history.
# This explicit mode instead verifies the smaller parent-provenance-v1 contract
# and its admission receipt, then emits the receipt shape consumed by the
# shared Stage 3 runner.  Every input is an already-held descriptor; display
# names are deliberately neither accepted nor reopened.
if [ "$stage2_parent_trust_root" = 1 ]; then
    stage2_parent_descriptor() {
        stage2_parent_tail=${1#/proc/}
        stage2_parent_pid=${stage2_parent_tail%%/*}
        stage2_parent_tail=${stage2_parent_tail#*/}
        stage2_parent_tag=${stage2_parent_tail%%/*}
        stage2_parent_fd=${stage2_parent_tail#*/}
        case "$stage2_parent_pid:$stage2_parent_fd" in
            *[!0-9:]*|0:*|:0|0*:*|*:0*) return 1 ;;
        esac
        [ "$stage2_parent_tag" = fd ] &&
            [ "$1" = "/proc/$stage2_parent_pid/fd/$stage2_parent_fd" ] &&
            [ -f "$1" ]
    }
    stage2_parent_value() {
        stage2_parent_key=$1
        stage2_parent_file=$2
        [ "$(grep -c "^${stage2_parent_key}=" "$stage2_parent_file")" = 1 ] || return 1
        sed -n "s/^${stage2_parent_key}=//p" "$stage2_parent_file"
    }
    for stage2_parent_input in "$manifest" "$candidate" "$source_snapshot" \
        "$runtime_snapshot" "$tool_snapshot" "$git_receipt" \
        "$stage2_admission" "$facade" "$authority_descriptor" \
        "$command_descriptor" "$sanity_descriptor" \
        "$manifest_write_descriptor" "$manifest_verify_descriptor" \
        "$self_test_descriptor" "$runner_descriptor"; do
        stage2_parent_descriptor "$stage2_parent_input" || exit 64
    done
    BOOTSTRAP_STAGE3_FACADE_PATH=$facade
    BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE=1
    BOOTSTRAP_STAGE3_AUTHORITY_DESCRIPTOR=$authority_descriptor
    BOOTSTRAP_STAGE3_COMMAND_DESCRIPTOR=$command_descriptor
    BOOTSTRAP_STAGE3_SANITY_DESCRIPTOR=$sanity_descriptor
    BOOTSTRAP_STAGE3_MANIFEST_WRITE_DESCRIPTOR=$manifest_write_descriptor
    BOOTSTRAP_STAGE3_MANIFEST_VERIFY_DESCRIPTOR=$manifest_verify_descriptor
    BOOTSTRAP_STAGE3_SELF_TEST_DESCRIPTOR=$self_test_descriptor
    BOOTSTRAP_STAGE3_RUNNER_DESCRIPTOR=$runner_descriptor
    export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE \
        BOOTSTRAP_STAGE3_AUTHORITY_DESCRIPTOR BOOTSTRAP_STAGE3_COMMAND_DESCRIPTOR \
        BOOTSTRAP_STAGE3_SANITY_DESCRIPTOR BOOTSTRAP_STAGE3_MANIFEST_WRITE_DESCRIPTOR \
        BOOTSTRAP_STAGE3_MANIFEST_VERIFY_DESCRIPTOR \
        BOOTSTRAP_STAGE3_SELF_TEST_DESCRIPTOR BOOTSTRAP_STAGE3_RUNNER_DESCRIPTOR
    . "$facade"
    stage2_parent_sha() { bootstrap_stage3_hash_file "$1"; }
    case "$run_id" in ????????|?????????*) ;; *) exit 64 ;; esac
    case "$run_id" in *[!A-Za-z0-9_-]*) exit 64 ;; esac
    [ "${#run_id}" -le 64 ] || exit 64
    case "$verifier_sha256" in ''|*[!0-9a-f]*) exit 64 ;; esac
    [ "${#verifier_sha256}" -eq 64 ] || exit 64
    [ "$(stage2_parent_sha "$0")" = "$verifier_sha256" ] || exit 65

    [ "$(wc -l <"$manifest" | tr -d ' ')" = 8 ] || exit 65
    [ "$(sed 's/=.*//' "$manifest" | LC_ALL=C sort | tr '\n' ',')" = \
        'admission_receipt_sha256,authority,candidate_sha256,runtime_snapshot_sha256,schema,source_snapshot_sha256,stage2-provenance,tool_authority_sha256,' ] || exit 65
    [ "$(stage2_parent_value schema "$manifest")" = \
        simple-bootstrap-stage2-parent-provenance-v1 ] || exit 65
    [ "$(stage2_parent_value stage2-provenance "$manifest")" = pure-simple ] || exit 65
    [ "$(stage2_parent_value authority "$manifest")" = \
        explicit-full-bootstrap-stage2-trust-root ] || exit 65
    stage2_parent_candidate_sha=$(stage2_parent_sha "$candidate") || exit 65
    stage2_parent_source_sha=$(stage2_parent_sha "$source_snapshot") || exit 65
    stage2_parent_runtime_sha=$(stage2_parent_sha "$runtime_snapshot") || exit 65
    stage2_parent_tool_sha=$(stage2_parent_sha "$tool_snapshot") || exit 65
    [ "$(stage2_parent_value candidate_sha256 "$manifest")" = \
        "$stage2_parent_candidate_sha" ] || exit 65
    [ "$(stage2_parent_value source_snapshot_sha256 "$manifest")" = \
        "$stage2_parent_source_sha" ] || exit 65
    [ "$(stage2_parent_value runtime_snapshot_sha256 "$manifest")" = \
        "$stage2_parent_runtime_sha" ] || exit 65
    [ "$(stage2_parent_value tool_authority_sha256 "$manifest")" = \
        "$stage2_parent_tool_sha" ] || exit 65
    [ "$(stage2_parent_value admission_receipt_sha256 "$manifest")" = \
        "$(stage2_parent_sha "$stage2_admission")" ] || exit 65
    [ "$(wc -l <"$stage2_admission" | tr -d ' ')" = 18 ] || exit 65
    [ "$(sed 's/=.*//' "$stage2_admission" | LC_ALL=C sort | tr '\n' ',')" = \
        'admission_identity,build_args_sha256,candidate_path,candidate_sha256,checks_executed_at_admission,checks_replayed_during_stage3,receiver_evidence_path,receiver_evidence_sha256,runtime_snapshot_path,runtime_snapshot_sha256,sanity_evidence_path,sanity_evidence_sha256,schema,source_snapshot_path,source_snapshot_sha256,status,tool_authority_path,tool_authority_sha256,' ] || exit 65
    [ "$(stage2_parent_value schema "$stage2_admission")" = \
        simple-bootstrap-stage2-admission-v1 ] || exit 65
    [ "$(stage2_parent_value status "$stage2_admission")" = admitted ] || exit 65
    [ "$(stage2_parent_value candidate_sha256 "$stage2_admission")" = \
        "$stage2_parent_candidate_sha" ] || exit 65
    [ "$(stage2_parent_value source_snapshot_sha256 "$stage2_admission")" = \
        "$stage2_parent_source_sha" ] || exit 65
    [ "$(stage2_parent_value runtime_snapshot_sha256 "$stage2_admission")" = \
        "$stage2_parent_runtime_sha" ] || exit 65
    [ "$(stage2_parent_value tool_authority_sha256 "$stage2_admission")" = \
        "$stage2_parent_tool_sha" ] || exit 65
    [ "$(stage2_parent_value checks_executed_at_admission "$stage2_admission")" = 1 ] || exit 65
    [ "$(stage2_parent_value checks_replayed_during_stage3 "$stage2_admission")" = 0 ] || exit 65

    printf '%s\n' \
        'schema=simple-stage3-provenance-verification-v1' \
        "run_id=$run_id" \
        "provenance_sha256=$(stage2_parent_sha "$manifest")" \
        "candidate_sha256=$stage2_parent_candidate_sha" \
        "source_snapshot_sha256=$stage2_parent_source_sha" \
        "runtime_snapshot_sha256=$stage2_parent_runtime_sha" \
        "tool_snapshot_sha256=$stage2_parent_tool_sha" \
        "git_receipt_sha256=$(stage2_parent_sha "$git_receipt")" \
        "verifier_sha256=$verifier_sha256" \
        'status=pass'
    exit 0
fi

case "$candidate_display" in /*) ;; *) exit 64 ;; esac
case "$manifest_display" in /*) ;; *) exit 64 ;; esac
case "$manifest_root_display" in /*) ;; *) exit 64 ;; esac
case "$facade_display" in /*) ;; *) exit 64 ;; esac
case "$admitted_compiler_display" in /*) ;; *) exit 64 ;; esac
case "$memory_display" in /*) ;; *) exit 64 ;; esac
case "$phase_display" in /*) ;; *) exit 64 ;; esac
case "$stage3_transcript_display" in /*) ;; *) exit 64 ;; esac
for descriptor_path in "$manifest" "$candidate" "$source_snapshot" \
    "$runtime_snapshot" "$tool_snapshot" "$git_receipt" "$launch_plan" \
    "$memory" "$phase" "$admitted_compiler" "$facade" \
    "$bootstrap_script_descriptor" "$candidate_frontend_descriptor" \
    "$authority_descriptor" "$command_descriptor" "$sanity_descriptor" \
    "$manifest_write_descriptor" "$manifest_verify_descriptor" \
    "$self_test_descriptor" "$runner_descriptor" \
    "$stage3_transcript_descriptor" "$helper_capsule_inventory" \
    "$bound_artifacts_descriptor" "$scratch_root"; do
    descriptor_tail=${descriptor_path#/proc/}
    descriptor_pid=${descriptor_tail%%/*}
    descriptor_tail=${descriptor_tail#*/}
    descriptor_tag=${descriptor_tail%%/*}
    descriptor_number=${descriptor_tail#*/}
    case "$descriptor_pid" in ''|0|0*|*[!0-9]*)
        echo "stage3 provenance verifier: non-descriptor input" >&2; exit 64 ;;
    esac
    [ "$descriptor_tag" = fd ] || {
        echo "stage3 provenance verifier: non-descriptor input" >&2; exit 64;
    }
    case "$descriptor_number" in ''|0|0*|*[!0-9]*)
        echo "stage3 provenance verifier: non-descriptor input" >&2; exit 64 ;;
    esac
    [ "$descriptor_path" = "/proc/$descriptor_pid/fd/$descriptor_number" ] || {
        echo "stage3 provenance verifier: non-descriptor input" >&2; exit 64;
    }
done

[ -d "$scratch_root/." ] || exit 64
scratch_identity=$(perl -e '
    my @st = stat($ARGV[0]);
    @st && (($st[2] & 07777) == 0700) && $st[4] == $< or exit 1;
    print "$st[0]:$st[1]\n";
' "$scratch_root") || exit 64
case "$scratch_identity" in
    *[!0-9:]*) exit 64 ;;
    *:*) ;;
    *) exit 64 ;;
esac

case "$run_id" in
    ????????|?????????*) ;;
    *) exit 64 ;;
esac
case "$run_id" in *[!A-Za-z0-9_-]*) exit 64 ;; esac
[ "${#run_id}" -le 64 ] || exit 64
for path in "$manifest" "$manifest_display" "$root" "$candidate" \
    "$source_snapshot" "$runtime_snapshot" "$tool_snapshot" "$git_receipt" \
    "$facade" "$facade_display" \
    "$launch_plan" "$memory" "$phase" "$admitted_compiler"; do
    case "$path" in /*) ;; *) exit 64 ;; esac
    case "$path" in *'
'*) exit 64 ;; esac
done
case "$verifier_sha256" in ''|*[!0-9a-f]*) exit 64 ;; esac
[ "${#verifier_sha256}" -eq 64 ] || exit 64
case "$launch_plan_sha256" in ''|*[!0-9a-f]*) exit 64 ;; esac
[ "${#launch_plan_sha256}" -eq 64 ] || exit 64
case "$helper_capsule_inventory_sha256" in ''|*[!0-9a-f]*) exit 64 ;; esac
[ "${#helper_capsule_inventory_sha256}" -eq 64 ] || exit 64
case "$helper_capsule_entry_parity_sha256" in ''|*[!0-9a-f]*) exit 64 ;; esac
[ "${#helper_capsule_entry_parity_sha256}" -eq 64 ] || exit 64

BOOTSTRAP_STAGE3_FACADE_PATH=$facade
BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE=1
BOOTSTRAP_STAGE3_BOOTSTRAP_SCRIPT_DESCRIPTOR=$bootstrap_script_descriptor
BOOTSTRAP_STAGE3_CANDIDATE_FRONTEND_DESCRIPTOR=$candidate_frontend_descriptor
BOOTSTRAP_STAGE3_BOUND_ARTIFACTS_DESCRIPTOR=$bound_artifacts_descriptor
BOOTSTRAP_STAGE3_MANIFEST_ROOT_DISPLAY=$manifest_root_display
replay_home_count=$(grep -c '^replay_home=' "$bound_artifacts_descriptor")
replay_tmpdir_count=$(grep -c '^replay_tmpdir=' "$bound_artifacts_descriptor")
[ "$replay_home_count" = 1 ] && [ "$replay_tmpdir_count" = 1 ] || exit 64
replay_home=$(sed -n 's/^replay_home=//p' "$bound_artifacts_descriptor")
replay_tmpdir=$(sed -n 's/^replay_tmpdir=//p' "$bound_artifacts_descriptor")
for replay_directory in "$replay_home" "$replay_tmpdir"; do
    replay_tail=${replay_directory#/proc/}
    replay_pid=${replay_tail%%/*}
    replay_tail=${replay_tail#*/}
    replay_tag=${replay_tail%%/*}
    replay_number=${replay_tail#*/}
    case "$replay_pid" in ''|0|0*|*[!0-9]*) exit 64 ;; esac
    [ "$replay_tag" = fd ] || exit 64
    case "$replay_number" in ''|0|0*|*[!0-9]*) exit 64 ;; esac
    [ "$replay_directory" = "/proc/$replay_pid/fd/$replay_number" ] || exit 64
    [ -d "$replay_directory/." ] || exit 64
done
HOME=$replay_home/.
TMPDIR=$replay_tmpdir/.
BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX=\
"$scratch_root/verify-$run_id-$$"
BOOTSTRAP_STAGE3_AUTHORITY_DESCRIPTOR=$authority_descriptor
BOOTSTRAP_STAGE3_COMMAND_DESCRIPTOR=$command_descriptor
BOOTSTRAP_STAGE3_SANITY_DESCRIPTOR=$sanity_descriptor
BOOTSTRAP_STAGE3_MANIFEST_WRITE_DESCRIPTOR=$manifest_write_descriptor
BOOTSTRAP_STAGE3_MANIFEST_VERIFY_DESCRIPTOR=$manifest_verify_descriptor
BOOTSTRAP_STAGE3_SELF_TEST_DESCRIPTOR=$self_test_descriptor
BOOTSTRAP_STAGE3_RUNNER_DESCRIPTOR=$runner_descriptor
export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_DESCRIPTOR_CAPSULE \
    BOOTSTRAP_STAGE3_BOOTSTRAP_SCRIPT_DESCRIPTOR \
    BOOTSTRAP_STAGE3_CANDIDATE_FRONTEND_DESCRIPTOR \
    BOOTSTRAP_STAGE3_BOUND_ARTIFACTS_DESCRIPTOR \
    BOOTSTRAP_STAGE3_MANIFEST_ROOT_DISPLAY \
    BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX \
    BOOTSTRAP_STAGE3_AUTHORITY_DESCRIPTOR BOOTSTRAP_STAGE3_COMMAND_DESCRIPTOR \
    BOOTSTRAP_STAGE3_SANITY_DESCRIPTOR BOOTSTRAP_STAGE3_MANIFEST_WRITE_DESCRIPTOR \
    BOOTSTRAP_STAGE3_MANIFEST_VERIFY_DESCRIPTOR \
    BOOTSTRAP_STAGE3_SELF_TEST_DESCRIPTOR BOOTSTRAP_STAGE3_RUNNER_DESCRIPTOR \
    HOME TMPDIR
. "$facade"

bootstrap_stage3_verifier_cleanup() {
    rm -f -- "${BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX}.runtime" \
        "${BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX}.tools" \
        "${BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX}.git-before" \
        "${BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX}.git-after" \
        "${BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX}.source" \
        "${BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX}.transcript-expected" \
        "${BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX}.transcript-host" \
        "${BOOTSTRAP_STAGE3_VERIFIER_SCRATCH_PREFIX}.frontend-replay"
}
trap bootstrap_stage3_verifier_cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

[ "$(bootstrap_stage3_hash_file "$0")" = "$verifier_sha256" ] || exit 65
[ "$(bootstrap_stage3_hash_file "$launch_plan")" = "$launch_plan_sha256" ] || exit 65
[ "$(bootstrap_stage3_hash_file "$helper_capsule_inventory")" = \
    "$helper_capsule_inventory_sha256" ] || exit 65
[ "$(bootstrap_stage3_manifest_value schema \
    "$helper_capsule_inventory")" = simple-stage3-helper-capsule-v1 ] || exit 65
[ "$(bootstrap_stage3_manifest_value status \
    "$helper_capsule_inventory")" = ready ] || exit 65
[ "$(bootstrap_stage3_manifest_value entry \
    "$helper_capsule_inventory")" = stage3 ] || exit 65
[ "$(bootstrap_stage3_manifest_value full_entry \
    "$helper_capsule_inventory")" = stage3 ] || exit 65
[ "$(bootstrap_stage3_manifest_value resume_entry \
    "$helper_capsule_inventory")" = stage3 ] || exit 65
[ "$(bootstrap_stage3_manifest_value helper_count \
    "$helper_capsule_inventory")" = 13 ] || exit 65
[ "$(bootstrap_stage3_manifest_value entry_parity_sha256 \
    "$helper_capsule_inventory")" = \
    "$helper_capsule_entry_parity_sha256" ] || exit 65
bootstrap_stage3_verify_manifest \
    "$manifest" "$root" "$candidate_display" "$manifest_display" >/dev/null

stage3_transcript=$(bootstrap_stage3_manifest_value \
    stage3_command_transcript_path "$manifest")
[ "$stage3_transcript" = "$stage3_transcript_display" ]
[ "$(bootstrap_stage3_transcript_explicit_env_value \
    "$stage3_transcript_descriptor" SIMPLE_EVIDENCE_RUN_ID)" = "$run_id" ]
[ "$(bootstrap_stage3_transcript_explicit_env_value \
    "$stage3_transcript_descriptor" SIMPLE_COMPILER_PHASE_PROFILE_FILE)" = "$phase_display" ]
[ "$(bootstrap_stage3_transcript_explicit_env_value \
    "$stage3_transcript_descriptor" SIMPLE_MEM_SNAPSHOT_FILE)" = "$memory_display" ]
[ "$(bootstrap_stage3_transcript_explicit_env_value \
    "$stage3_transcript_descriptor" SIMPLE_BINARY)" = "$admitted_compiler_display" ]
[ "$(bootstrap_stage3_manifest_value stage2_admitted_path "$manifest")" = \
    "$admitted_compiler_display" ]

printf '%s\n' \
    'schema=simple-stage3-provenance-verification-v1' \
    "run_id=$run_id" \
    "provenance_sha256=$(bootstrap_stage3_hash_file "$manifest")" \
    "candidate_sha256=$(bootstrap_stage3_hash_file "$candidate")" \
    "source_snapshot_sha256=$(bootstrap_stage3_hash_file "$source_snapshot")" \
    "runtime_snapshot_sha256=$(bootstrap_stage3_hash_file "$runtime_snapshot")" \
    "tool_snapshot_sha256=$(bootstrap_stage3_hash_file "$tool_snapshot")" \
    "git_receipt_sha256=$(bootstrap_stage3_hash_file "$git_receipt")" \
    "verifier_sha256=$verifier_sha256" \
    'status=pass'
