#!/bin/sh
# Compatibility supervisor for the staged bootstrap trust engine.
#
# The existing engine remains the only producer/admission authority. This
# supervisor adds scheduling: it watches the immutable Stage-2 smoke receipt,
# qualifies that parent while the engine builds Stage 3, and admits/deploys no
# descendant until the parent qualification and generation lease both pass.
set -eu

entry_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P) || exit 70
root=$(CDPATH= cd -- "$entry_dir/../.." && pwd -P) || exit 70
contract="$entry_dir/bootstrap-scheduler-contract.shs"
graph_contract="$entry_dir/bootstrap-graph.sdn"
. "$contract"
BOOTSTRAP_STAGE3_FACADE_PATH="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT=$root
export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_VERSION_ROOT
. "$BOOTSTRAP_STAGE3_FACADE_PATH"

usage() {
    cat <<'EOF'
usage: bootstrap-strategy.sh --strategy=adhoc|normal|full --output=DIR -- ENGINE_ARGS...

The arguments after -- are the original bootstrap-from-scratch.sh arguments.
adhoc delegates unchanged. normal/full create a generation lease and run the
Stage-2 qualification DAG. clean-release and one-binary remain on the legacy
engine until their isolated continuation contracts are implemented.
EOF
}

strategy=normal
output_arg=build/bootstrap
while [ "$#" -gt 0 ]; do
    case "$1" in
        --strategy=*) strategy=${1#*=} ;;
        --output=*) output_arg=${1#*=} ;;
        --) shift; break ;;
        --help|-h) usage; exit 0 ;;
        *) echo "bootstrap-scheduler-error: unknown supervisor option: $1" >&2; exit 2 ;;
    esac
    shift
done
[ "$#" -gt 0 ] || {
    echo 'bootstrap-scheduler-error: missing stage-engine arguments after --' >&2
    exit 2
}
case "$strategy" in adhoc|normal|full) ;; *)
    echo "bootstrap-scheduler-error: unknown strategy: $strategy" >&2
    exit 2
esac

engine="$entry_dir/bootstrap-from-scratch.sh"
qualifier="$entry_dir/bootstrap-qualify-stage2.shs"
[ -f "$engine" ] && [ ! -L "$engine" ] || exit 2
[ -f "$qualifier" ] && [ ! -L "$qualifier" ] || exit 2

if [ "$strategy" = adhoc ]; then
    SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1 \
        exec /bin/sh "$engine" "$@"
fi

wants_full_cli=0
wants_deploy=0
wants_release=0
unsupported=
receipt=
backend=llvm
mode=dynload
no_mcp=0
for original_arg in "$@"; do
    case "$original_arg" in
        --full-cli) wants_full_cli=1 ;;
        --deploy) wants_deploy=1; wants_full_cli=1 ;;
        --release) wants_release=1; wants_deploy=1; wants_full_cli=1 ;;
        --clean-release) unsupported=clean-release ;;
        --mode=one-binary) unsupported=one-binary ;;
        --mode=*) mode=${original_arg#*=} ;;
        --backend=*) backend=${original_arg#*=} ;;
        --bootstrap-receipt=*) receipt=${original_arg#*=} ;;
        --no-mcp) no_mcp=1 ;;
    esac
done
[ -n "$receipt" ] || receipt=${SIMPLE_BOOTSTRAP_REASON_RECEIPT:-}
# Preserve the stage engine's canonical receipt preflight and exit code. The
# supervisor must not turn an authorization refusal into a scheduler failure.
if [ -z "$receipt" ]; then
    SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1 \
        exec /bin/sh "$engine" "$@"
fi
[ -z "$unsupported" ] || {
    echo "bootstrap-scheduler-error: $unsupported requires the legacy monolithic path; use --strategy=adhoc until its isolated continuation contract exists" >&2
    exit 78
}
[ "$mode" = dynload ] || {
    echo "bootstrap-scheduler-error: unsupported coordinated mode: $mode" >&2
    exit 78
}
bootstrap_scheduler_validate_graph_contract "$graph_contract" || {
    echo 'bootstrap-scheduler-error: bootstrap graph contract is invalid' >&2
    exit 2
}

case "$output_arg" in
    '') exit 2 ;;
    *../*|../*|*/..|..) echo 'bootstrap-scheduler-error: output may not contain .. components' >&2; exit 2 ;;
    /*) output=$output_arg ;;
    *) output="$root/$output_arg" ;;
esac
[ ! -L "$output" ] || {
    echo 'bootstrap-scheduler-error: output root may not be a symlink' >&2
    exit 2
}
mkdir -p "$output"
output=$(CDPATH= cd -- "$output" && pwd -P)

scheduler_lock="${output}.scheduler-lock"
mkdir "$scheduler_lock" 2>/dev/null || {
    echo "bootstrap-scheduler-error: scheduler output is already owned: $output" >&2
    exit 73
}
engine_pid=
qualifier_pid=
cleanup() {
    [ -z "$qualifier_pid" ] || kill "$qualifier_pid" 2>/dev/null || true
    [ -z "$engine_pid" ] || kill "$engine_pid" 2>/dev/null || true
    rm -rf "$scheduler_lock"
}
trap cleanup EXIT HUP INT TERM

epoch=$(date -u +%Y%m%dT%H%M%SZ)
generation="bootstrap-$epoch-$$"
generation_dir="$output/scheduler/$generation"
mkdir -p "$generation_dir/tasks" "$generation_dir/invalidations"

graph_sha=$(bootstrap_scheduler_hash_file "$graph_contract") || exit 2
policy_sha=absent
[ ! -f "$root/.spipe/policy/vcs.sdn" ] ||
    policy_sha=$(bootstrap_scheduler_hash_file "$root/.spipe/policy/vcs.sdn")
input_digest() {
    {
        git -C "$root" rev-parse HEAD 2>/dev/null || echo no-git-head
        git -C "$root" status --porcelain=v1 --untracked-files=all -- \
            src/compiler src/lib src/app scripts/bootstrap scripts/check \
            .spipe/policy release VERSION 2>/dev/null || true
        git -C "$root" diff --no-ext-diff --binary HEAD -- \
            src/compiler src/lib src/app scripts/bootstrap scripts/check \
            .spipe/policy release VERSION 2>/dev/null || true
    } | bootstrap_scheduler_hash_stream
}
source_digest=$(input_digest) || exit 2

cpu_total=${SIMPLE_BOOTSTRAP_SCHEDULER_CPU_SLOTS:-}
if [ -z "$cpu_total" ]; then
    cpu_total=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
fi
case "$cpu_total" in ''|*[!0-9]*|0) cpu_total=1 ;; esac
if [ "$cpu_total" -gt 1 ]; then
    qualification_cpu=1
    critical_cpu=$((cpu_total - qualification_cpu))
else
    qualification_cpu=0
    critical_cpu=1
fi
memory_total=${SIMPLE_BOOTSTRAP_SCHEDULER_MEMORY_MIB:-}
if [ -z "$memory_total" ] && [ -r /proc/meminfo ]; then
    memory_total=$(awk '/^MemTotal:/ {print int($2 / 1024); exit}' /proc/meminfo)
fi
case "$memory_total" in ''|*[!0-9]*|0) memory_total=2048 ;; esac
qualification_memory=${SIMPLE_BOOTSTRAP_QUALIFICATION_MEMORY_MIB:-2048}
memory_safety=${SIMPLE_BOOTSTRAP_SCHEDULER_MEMORY_SAFETY_MIB:-1024}
critical_memory=${SIMPLE_BOOTSTRAP_CRITICAL_MEMORY_MIB:-}
case "$qualification_memory:$memory_safety" in
    *[!0-9:]*|0:*|*:0) echo 'bootstrap-scheduler-error: invalid memory reservation' >&2; exit 2 ;;
esac
if [ -z "$critical_memory" ]; then
    critical_memory=$((memory_total - qualification_memory - memory_safety))
    [ "$critical_memory" -gt 0 ] || critical_memory=$memory_total
fi
case "$critical_memory" in ''|*[!0-9]*|0) echo 'bootstrap-scheduler-error: invalid compiler memory limit' >&2; exit 2 ;; esac
memory_enforcement=none
if (ulimit -v 1048576) 2>/dev/null; then
    memory_enforcement=ulimit-v
fi
schedule_mode=speculative
if [ "$qualification_cpu" -eq 0 ] || [ "$memory_enforcement" = none ] ||
   [ "$memory_total" -lt $((qualification_memory + critical_memory + memory_safety)) ]; then
    schedule_mode=serialized-resource-guard
    qualification_cpu=$cpu_total
    critical_cpu=$cpu_total
fi

runtime_graph_tmp="$generation_dir/graph.env.tmp.$$"
{
    echo schema=simple-bootstrap-runtime-graph-v1
    echo generation="$generation"
    echo strategy="$strategy"
    echo static_graph_path="$graph_contract"
    echo static_graph_sha256="$graph_sha"
    echo source_generation_sha256="$source_digest"
    echo policy_sha256="$policy_sha"
    echo schedule_mode="$schedule_mode"
    echo cpu_total="$cpu_total"
    echo cpu_compiler_critical="$critical_cpu"
    echo cpu_qualification="$qualification_cpu"
    echo memory_total_mib="$memory_total"
    echo memory_enforcement="$memory_enforcement"
    echo memory_safety_mib="$memory_safety"
    echo memory_compiler_reservation_mib="$critical_memory"
    echo memory_qualification_mib="$qualification_memory"
    echo deploy_token=exclusive
    echo quarantine_root="$output"
} >"$runtime_graph_tmp"
bootstrap_scheduler_atomic_replace "$runtime_graph_tmp" "$generation_dir/graph.env"
runtime_graph_sha=$(bootstrap_scheduler_hash_file "$generation_dir/graph.env")

lease="$generation_dir/generation.lease.env"
lease_tmp="$lease.tmp.$$"
{
    echo schema=simple-bootstrap-generation-lease-v1
    echo generation="$generation"
    echo status=current
    echo owner_pid="$$"
    echo source_generation_sha256="$source_digest"
    echo policy_sha256="$policy_sha"
    echo graph_sha256="$runtime_graph_sha"
    echo created_epoch_seconds="$(date +%s)"
} >"$lease_tmp"
bootstrap_scheduler_atomic_replace "$lease_tmp" "$lease"
lease_sha=$(bootstrap_scheduler_hash_file "$lease")

current_tmp="$output/scheduler/current.env.tmp.$$"
{
    echo schema=simple-bootstrap-current-generation-v1
    echo generation="$generation"
    echo generation_dir="$generation_dir"
    echo lease_sha256="$lease_sha"
    echo status=running
} >"$current_tmp"
bootstrap_scheduler_atomic_replace "$current_tmp" "$output/scheduler/current.env"

events="$generation_dir/events.env"
event() {
    printf 'schema=simple-bootstrap-event-v1 generation=%s epoch_seconds=%s event=%s task=%s status=%s\n' \
        "$generation" "$(date +%s)" "$1" "$2" "$3" >>"$events"
}

engine_done="$generation_dir/engine.done.env"
engine_started=$(date +%s)
event task-start stage-engine building
(
    set +e
    if [ "$memory_enforcement" = ulimit-v ]; then
        ulimit -v $((critical_memory * 1024)) || exit 70
    fi
    SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1 \
    SIMPLE_BOOTSTRAP_STAGE2_CLEANUP_MARKER="$generation_dir/stage2-cleanup.ready" \
    SIMPLE_BOOTSTRAP_QUALIFICATION_CPU_SLOTS="$qualification_cpu" \
    perl -e '
        use strict; use warnings;
        my $jobs = shift @ARGV;
        my $engine = shift @ARGV;
        my @out;
        my $skip_value = 0;
        for my $arg (@ARGV) {
            if ($skip_value) { $skip_value = 0; next; }
            if ($arg eq "--jobs") { $skip_value = 1; next; }
            next if $arg =~ /^--jobs=/;
            next if $arg eq "--full-cli" || $arg eq "--deploy" ||
                $arg eq "--release" || $arg eq "--clean-release";
            push @out, $arg;
        }
        push @out, "--jobs=$jobs";
        exec "/bin/sh", $engine, @out;
        die "exec stage engine failed: $!";
    ' "$critical_cpu" "$engine" "$@" \
        >"$generation_dir/stage-engine.log" 2>&1
    rc=$?
    done_tmp="$engine_done.tmp.$$"
    {
        echo schema=simple-bootstrap-task-exit-v1
        echo generation="$generation"
        echo task=stage-engine
        echo exit_code="$rc"
        echo completed_epoch_seconds="$(date +%s)"
    } >"$done_tmp"
    chmod 400 "$done_tmp"
    mv "$done_tmp" "$engine_done"
    exit "$rc"
) &
engine_pid=$!

run_qualifier() {
    (
        if [ "$memory_enforcement" = ulimit-v ]; then
            ulimit -v $((qualification_memory * 1024)) || exit 70
        fi
        SIMPLE_BOOTSTRAP_QUALIFICATION_CPU_SLOTS="$qualification_cpu" \
            /bin/sh "$qualifier" "$output" "$generation_dir" "$lease" \
            "$lease_sha" "$engine_done"
    ) >"$generation_dir/qualification.log" 2>&1
}

qualifier_started=0
if [ "$schedule_mode" = speculative ]; then
    run_qualifier &
    qualifier_pid=$!
    qualifier_started=1
fi

if [ "$qualifier_started" -eq 1 ]; then
    set +e
    wait "$qualifier_pid"
    qualifier_rc=$?
    set -e
    qualifier_pid=
    if [ "$qualifier_rc" -ne 0 ] && [ "$strategy" = normal ]; then
        kill -TERM "-$engine_pid" 2>/dev/null || kill "$engine_pid" 2>/dev/null || true
    fi
else
    qualifier_rc=not-run
fi

set +e
wait "$engine_pid"
engine_rc=$?
set -e
engine_pid=
engine_finished=$(bootstrap_scheduler_manifest_value completed_epoch_seconds \
    "$engine_done" 2>/dev/null || date +%s)

if [ "$qualifier_started" -eq 0 ] && [ "$engine_rc" -eq 0 ]; then
    set +e
    run_qualifier
    qualifier_rc=$?
    set -e
elif [ "$qualifier_started" -eq 0 ]; then
    qualifier_rc=1
fi

write_task_receipt() {
    task_name=$1 task_status=$2 task_rc=$3 task_started=$4 task_completed=$5
    task_output_class=${6:-quarantined}
    task_tmp="$generation_dir/tasks/$task_name.env.tmp.$$"
    {
        echo schema=simple-bootstrap-task-receipt-v1
        echo generation="$generation"
        echo lease_sha256="$lease_sha"
        echo task="$task_name"
        echo status="$task_status"
        echo exit_code="$task_rc"
        echo started_epoch_seconds="$task_started"
        echo completed_epoch_seconds="$task_completed"
        echo output_class="$task_output_class"
    } >"$task_tmp"
    bootstrap_scheduler_atomic_replace "$task_tmp" \
        "$generation_dir/tasks/$task_name.env"
}

[ "$engine_rc" -eq 0 ] && engine_status=passed || engine_status=failed
write_task_receipt stage-engine "$engine_status" "$engine_rc" \
    "$engine_started" "$engine_finished"
qualification_started=$(bootstrap_scheduler_manifest_value epoch_seconds \
    "$generation_dir/qualification.started" 2>/dev/null || date +%s)
qualification_finished=$(bootstrap_scheduler_manifest_value completed_epoch_seconds \
    "$generation_dir/qualification.result.env" 2>/dev/null || date +%s)
if [ "$qualifier_rc" = 0 ] &&
   [ "$(bootstrap_scheduler_manifest_value status \
       "$generation_dir/qualification.result.env" 2>/dev/null || true)" = passed ]; then
    qualification_status=passed
else
    qualification_status=failed
fi
write_task_receipt stage2-qualification "$qualification_status" \
    "$qualifier_rc" "$qualification_started" "$qualification_finished"

qualification_result="$generation_dir/qualification.result.env"
qualification_evidence_status=invalid
if [ "$qualification_status" = passed ] &&
   bootstrap_scheduler_verify_qualification_result "$qualification_result" \
       "$generation" "$lease_sha" "$output" "$generation_dir"; then
    qualification_admission=$(bootstrap_scheduler_manifest_value admission_path \
        "$qualification_result" 2>/dev/null || true)
    qualification_candidate=$(bootstrap_scheduler_manifest_value candidate_path \
        "$qualification_result" 2>/dev/null || true)
    admission_source=$(bootstrap_scheduler_manifest_value source_snapshot_path \
        "$qualification_admission" 2>/dev/null || true)
    admission_runtime=$(bootstrap_scheduler_manifest_value runtime_snapshot_path \
        "$qualification_admission" 2>/dev/null || true)
    admission_tool=$(bootstrap_scheduler_manifest_value tool_authority_path \
        "$qualification_admission" 2>/dev/null || true)
    admission_args=$(bootstrap_scheduler_manifest_value build_args_sha256 \
        "$qualification_admission" 2>/dev/null || true)
    admission_sanity=$(bootstrap_scheduler_manifest_value sanity_evidence_path \
        "$qualification_admission" 2>/dev/null || true)
    admission_receiver=$(bootstrap_scheduler_manifest_value receiver_evidence_path \
        "$qualification_admission" 2>/dev/null || true)
    if bootstrap_stage3_verify_stage2_admission_receipt \
        "$qualification_admission" "$qualification_candidate" \
        "$admission_source" "$admission_runtime" "$admission_tool" \
        "$admission_args" "$admission_sanity" "$admission_receiver" "$root"; then
        qualification_evidence_status=verified
    fi
fi

stage3_evidence_status=invalid
stage3_manifest=
stage3_candidate=
stage3_result="$generation_dir/stage3.result.env"
set -- "$output"/stage3/*/provenance.env
stage3_manifest_count=0
for stage3_manifest_candidate in "$@"; do
    if [ -f "$stage3_manifest_candidate" ] && [ ! -L "$stage3_manifest_candidate" ]; then
        stage3_manifest=$stage3_manifest_candidate
        stage3_manifest_count=$((stage3_manifest_count + 1))
    fi
done
if [ "$stage3_manifest_count" -eq 1 ]; then
    stage3_candidate=$(bootstrap_stage3_manifest_value stage3_path \
        "$stage3_manifest" 2>/dev/null || true)
    qualification_admission=$(bootstrap_scheduler_manifest_value admission_path \
        "$qualification_result" 2>/dev/null || true)
    qualification_admission_sha=$(bootstrap_scheduler_manifest_value admission_sha256 \
        "$qualification_result" 2>/dev/null || true)
    manifest_admission=$(bootstrap_stage3_manifest_value \
        stage2_admission_receipt_path "$stage3_manifest" 2>/dev/null || true)
    manifest_admission_sha=$(bootstrap_stage3_manifest_value \
        stage2_admission_receipt_sha256 "$stage3_manifest" 2>/dev/null || true)
    if [ "$qualification_evidence_status" = verified ] &&
       [ "$manifest_admission" = "$qualification_admission" ] &&
       [ "$manifest_admission_sha" = "$qualification_admission_sha" ] &&
       bootstrap_stage3_verify_manifest "$stage3_manifest" "$root" \
           "$stage3_candidate"; then
        stage3_tmp="$stage3_result.tmp.$$"
        {
            echo schema=simple-bootstrap-stage3-scheduler-result-v1
            echo generation="$generation"
            echo status=verified
            echo lease_sha256="$lease_sha"
            echo provenance_path="$stage3_manifest"
            echo provenance_sha256="$(bootstrap_scheduler_hash_file "$stage3_manifest")"
            echo candidate_path="$stage3_candidate"
            echo candidate_sha256="$(bootstrap_scheduler_hash_file "$stage3_candidate")"
            echo parent_admission_path="$qualification_admission"
            echo parent_admission_sha256="$qualification_admission_sha"
        } >"$stage3_tmp"
        bootstrap_scheduler_atomic_replace "$stage3_tmp" "$stage3_result"
        if bootstrap_scheduler_verify_stage3_result "$stage3_result" \
            "$generation" "$lease_sha" "$output"; then
            stage3_evidence_status=verified
        fi
    fi
fi

overlap_observed=false
if [ "$schedule_mode" = speculative ] &&
   [ "$qualification_started" -lt "$engine_finished" ]; then
    overlap_observed=true
fi

failure_root=
failure_reason=
if [ "$engine_status" != passed ]; then
    failure_root=stage2
    failure_reason=stage-engine-failed
elif [ "$qualification_status" != passed ]; then
    failure_root=stage2
    case "$qualifier_rc" in 75) failure_reason=stale-generation-lease ;; *) failure_reason=parent-qualification-failed ;; esac
elif [ "$qualification_evidence_status" != verified ]; then
    failure_root=stage2
    failure_reason=qualification-evidence-invalid
elif [ "$stage3_evidence_status" != verified ]; then
    failure_root=stage3
    failure_reason=stage3-provenance-invalid
elif ! bootstrap_scheduler_lease_current "$lease" "$generation" "$lease_sha"; then
    failure_root=stage2
    failure_reason=stale-generation-lease
elif [ "$(input_digest)" != "$source_digest" ]; then
    failure_root=stage2
    failure_reason=source-or-policy-drift
fi

if [ -n "$failure_root" ]; then
    tainted_tmp="$lease.tmp.$$"
    {
        echo schema=simple-bootstrap-generation-lease-v1
        echo generation="$generation"
        echo status=tainted
        echo previous_lease_sha256="$lease_sha"
        echo reason="$failure_reason"
        echo tainted_epoch_seconds="$(date +%s)"
    } >"$tainted_tmp"
    bootstrap_scheduler_atomic_replace "$tainted_tmp" "$lease"
    bootstrap_scheduler_write_invalidation \
        "$generation_dir/invalidations" "$generation" "$failure_root" \
        "$failure_reason" "$lease_sha"
    failure_tmp="$generation_dir/failure-manifest.env.tmp.$$"
    {
        echo schema=simple-bootstrap-failure-manifest-v1
        echo generation="$generation"
        echo status=failed
        echo failure_root="$failure_root"
        echo failure_reason="$failure_reason"
        echo source_generation_sha256="$source_digest"
        echo policy_sha256="$policy_sha"
        echo lease_sha256="$lease_sha"
        echo graph_sha256="$runtime_graph_sha"
        echo tasks_selected=2
        echo tasks_complete=2
        echo stage_engine_status="$engine_status"
        echo stage2_qualification_status="$qualification_status"
        echo overlap_observed="$overlap_observed"
        echo descendants=recursively-invalidated
        echo artifacts=preserved-tainted
    } >"$failure_tmp"
    bootstrap_scheduler_atomic_replace "$failure_tmp" \
        "$generation_dir/failure-manifest.env"
    failed_current_tmp="$output/scheduler/current.env.tmp.$$"
    {
        echo schema=simple-bootstrap-current-generation-v1
        echo generation="$generation"
        echo generation_dir="$generation_dir"
        echo lease_sha256="$(bootstrap_scheduler_hash_file "$lease")"
        echo status=failed
        echo failure_manifest="$generation_dir/failure-manifest.env"
    } >"$failed_current_tmp"
    bootstrap_scheduler_atomic_replace "$failed_current_tmp" \
        "$output/scheduler/current.env"
    event generation-invalidated "$failure_root" "$failure_reason"
    echo "bootstrap-scheduler-error: $failure_reason; evidence: $generation_dir/failure-manifest.env" >&2
    exit 1
fi

bootstrap_scheduler_verify_task_receipt \
    "$generation_dir/tasks/stage-engine.env" "$generation" "$lease_sha" \
    stage-engine || exit 1
bootstrap_scheduler_verify_task_receipt \
    "$generation_dir/tasks/stage2-qualification.env" "$generation" \
    "$lease_sha" stage2-qualification || exit 1

# This immutable admission is the authority for every Stage-4/deploy/release
# continuation. It is written and re-verified while the generation lease is
# still current, before the continuation process is allowed to start.
lineage_tmp="$generation_dir/lineage-admission.env.tmp.$$"
{
    echo schema=simple-bootstrap-lineage-admission-v1
    echo generation="$generation"
    echo status=qualified
    echo bootstrap_output="$output"
    echo generation_lease_path="$lease"
    echo lease_sha256="$lease_sha"
    echo graph_sha256="$runtime_graph_sha"
    echo source_generation_sha256="$source_digest"
    echo qualification_result_path="$qualification_result"
    echo qualification_result_sha256="$(bootstrap_scheduler_hash_file "$qualification_result")"
    echo stage3_result_path="$stage3_result"
    echo stage3_result_sha256="$(bootstrap_scheduler_hash_file "$stage3_result")"
    echo stage3_provenance_path="$stage3_manifest"
    echo stage3_provenance_sha256="$(bootstrap_scheduler_hash_file "$stage3_manifest")"
    echo stage3_candidate_path="$stage3_candidate"
    echo stage3_candidate_sha256="$(bootstrap_scheduler_hash_file "$stage3_candidate")"
    echo parent_admission_path="$qualification_admission"
    echo parent_admission_sha256="$qualification_admission_sha"
    echo stage_engine_receipt_sha256="$(bootstrap_scheduler_hash_file "$generation_dir/tasks/stage-engine.env")"
    echo stage2_qualification_receipt_sha256="$(bootstrap_scheduler_hash_file "$generation_dir/tasks/stage2-qualification.env")"
    echo overlap_observed="$overlap_observed"
    echo schedule_mode="$schedule_mode"
    echo ancestor_chain=qualified-untainted
    echo completed_epoch_seconds="$(date +%s)"
} >"$lineage_tmp"
bootstrap_scheduler_atomic_replace "$lineage_tmp" \
    "$generation_dir/lineage-admission.env"
lineage="$generation_dir/lineage-admission.env"
lineage_sha=$(bootstrap_scheduler_hash_file "$lineage")
bootstrap_scheduler_verify_lineage_admission "$lineage" "$generation" \
    "$lease_sha" "$output" || {
    echo 'bootstrap-scheduler-error: lineage admission did not re-verify' >&2
    exit 1
}

verify_continuation_evidence() {
    continuation_receipt="$output/stage4-continuation.env"
    [ "$(bootstrap_scheduler_manifest_value schema "$continuation_receipt")" = \
        simple-bootstrap-stage4-continuation-v1 ] || return 1
    [ "$(bootstrap_scheduler_manifest_value status "$continuation_receipt")" = pass ] || return 1
    [ "$(bootstrap_scheduler_manifest_value lineage_path "$continuation_receipt")" = \
        "$lineage" ] || return 1
    [ "$(bootstrap_scheduler_manifest_value lineage_sha256 "$continuation_receipt")" = \
        "$lineage_sha" ] || return 1
    [ "$(bootstrap_scheduler_manifest_value stage3_provenance_path \
        "$continuation_receipt")" = "$stage3_manifest" ] || return 1
    [ "$(bootstrap_scheduler_manifest_value stage3_provenance_sha256 \
        "$continuation_receipt")" = \
        "$(bootstrap_scheduler_hash_file "$stage3_manifest")" ] || return 1
    for continuation_stem in planner_receipt parent_compiler immutable_snapshot \
        immutable_after stage4_output stage4_provenance; do
        continuation_path=$(bootstrap_scheduler_manifest_value \
            "${continuation_stem}_path" "$continuation_receipt") || return 1
        continuation_hash=$(bootstrap_scheduler_manifest_value \
            "${continuation_stem}_sha256" "$continuation_receipt") || return 1
        case "$continuation_stem" in
            planner_receipt) continuation_path_root=$root ;;
            *) continuation_path_root=$output ;;
        esac
        bootstrap_scheduler_path_within "$continuation_path_root" \
            "$continuation_path" || return 1
        [ "$(bootstrap_scheduler_hash_file "$continuation_path")" = \
            "$continuation_hash" ] || return 1
    done
    publication_status=$(bootstrap_scheduler_manifest_value publication_status \
        "$continuation_receipt") || return 1
    case "$publication_status" in
        quarantined)
            [ "$(bootstrap_scheduler_manifest_value deploy_receipt_path \
                "$continuation_receipt")" = not-published ] || return 1
            [ "$(bootstrap_scheduler_manifest_value deploy_receipt_sha256 \
                "$continuation_receipt")" = not-published ] || return 1
            ;;
        deployed)
            [ "$wants_deploy" -eq 1 ] || return 1
            deploy_receipt=$(bootstrap_scheduler_manifest_value deploy_receipt_path \
                "$continuation_receipt") || return 1
            deploy_receipt_sha=$(bootstrap_scheduler_manifest_value deploy_receipt_sha256 \
                "$continuation_receipt") || return 1
            bootstrap_scheduler_path_within "$root" "$deploy_receipt" || return 1
            [ "$(bootstrap_scheduler_hash_file "$deploy_receipt")" = \
                "$deploy_receipt_sha" ] || return 1
            stage4_hash=$(bootstrap_scheduler_manifest_value stage4_output_sha256 \
                "$continuation_receipt") || return 1
            bootstrap_scheduler_verify_deploy_receipt "$deploy_receipt" \
                "$root" "$stage4_hash" || return 1
            ;;
        *) return 1 ;;
    esac
    continuation_result="$generation_dir/stage4.result.env"
    continuation_tmp="$continuation_result.tmp.$$"
    {
        echo schema=simple-bootstrap-stage4-scheduler-result-v1
        echo generation="$generation"
        echo status=verified
        echo lease_sha256="$lease_sha"
        echo publication_status="$publication_status"
        echo continuation_path="$continuation_receipt"
        echo continuation_sha256="$(bootstrap_scheduler_hash_file "$continuation_receipt")"
        echo lineage_path="$lineage"
        echo lineage_sha256="$lineage_sha"
        echo stage3_provenance_path="$stage3_manifest"
        echo stage3_provenance_sha256="$(bootstrap_scheduler_hash_file "$stage3_manifest")"
        echo stage4_path="$(bootstrap_scheduler_manifest_value stage4_output_path "$continuation_receipt")"
        echo stage4_sha256="$(bootstrap_scheduler_manifest_value stage4_output_sha256 "$continuation_receipt")"
        echo stage4_provenance_path="$(bootstrap_scheduler_manifest_value stage4_provenance_path "$continuation_receipt")"
        echo stage4_provenance_sha256="$(bootstrap_scheduler_manifest_value stage4_provenance_sha256 "$continuation_receipt")"
    } >"$continuation_tmp"
    bootstrap_scheduler_atomic_replace "$continuation_tmp" "$continuation_result"
    bootstrap_scheduler_verify_continuation_result "$continuation_result" \
        "$generation" "$lease_sha" "$output" "$publication_status"
}

# Stage 4/publication is a continuation, never part of provisional-parent
# speculation. It begins only after the qualified Stage-2/3 lineage above.
continuation_status=not-requested
if [ "$wants_full_cli" -eq 1 ]; then
    [ -n "$receipt" ] || {
        echo 'bootstrap-scheduler-error: Stage-4 continuation requires --bootstrap-receipt' >&2
        exit 64
    }
    continuation_status=failed
    continuation_started=$(date +%s)
    set -- --strategy="$strategy" --output="$output_arg" \
        --resume-stage4-from-admitted="$output_arg" \
        --bootstrap-receipt="$receipt" --backend="$backend" \
        --mode=dynload --jobs="$critical_cpu" --full-cli
    [ "$no_mcp" -eq 0 ] || set -- "$@" --no-mcp
    # Stage 4 is always a build-only quarantine invocation. Publication cannot
    # occur inside this long-running child because the supervisor must recheck
    # the lease and every bound input after the child exits.
    continuation_quarantine=1
    set +e
    env SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1 \
        SIMPLE_BOOTSTRAP_STAGE4_QUARANTINE="$continuation_quarantine" \
        SIMPLE_BOOTSTRAP_LINEAGE_ADMISSION="$lineage" \
        SIMPLE_BOOTSTRAP_LINEAGE_ADMISSION_SHA256="$lineage_sha" \
        /bin/sh "$engine" "$@" \
        >"$generation_dir/stage4-continuation.log" 2>&1
    continuation_rc=$?
    set -e
    continuation_finished=$(date +%s)
    if [ "$continuation_rc" -eq 0 ] && verify_continuation_evidence; then
        continuation_status=passed
    elif [ "$continuation_rc" -eq 0 ]; then
        continuation_rc=1
        echo 'bootstrap-scheduler-error: Stage-4 evidence did not re-verify' \
            >>"$generation_dir/stage4-continuation.log"
    fi
    continuation_output_class=quarantined
    write_task_receipt stage4-continuation "$continuation_status" \
        "$continuation_rc" "$continuation_started" "$continuation_finished" \
        "$continuation_output_class"
    if [ "$continuation_status" != passed ]; then
        failure_root=stage4
        failure_reason=stage4-continuation-failed
        tainted_tmp="$lease.tmp.$$"
        {
            echo schema=simple-bootstrap-generation-lease-v1
            echo generation="$generation"
            echo status=tainted
            echo previous_lease_sha256="$lease_sha"
            echo reason="$failure_reason"
            echo tainted_epoch_seconds="$(date +%s)"
        } >"$tainted_tmp"
        bootstrap_scheduler_atomic_replace "$tainted_tmp" "$lease"
        bootstrap_scheduler_write_invalidation \
            "$generation_dir/invalidations" "$generation" stage4 \
            "$failure_reason" "$lease_sha"
        failure_tmp="$generation_dir/failure-manifest.env.tmp.$$"
        {
            echo schema=simple-bootstrap-failure-manifest-v1
            echo generation="$generation"
            echo status=failed
            echo failure_root=stage4
            echo failure_reason="$failure_reason"
            echo source_generation_sha256="$source_digest"
            echo policy_sha256="$policy_sha"
            echo lease_sha256="$lease_sha"
            echo graph_sha256="$runtime_graph_sha"
            echo tasks_selected=3
            echo tasks_complete=3
            echo stage_engine_status="$engine_status"
            echo stage2_qualification_status="$qualification_status"
            echo stage4_continuation_status="$continuation_status"
            echo overlap_observed="$overlap_observed"
            echo descendants=recursively-invalidated
            echo artifacts=preserved-tainted
        } >"$failure_tmp"
        bootstrap_scheduler_atomic_replace "$failure_tmp" \
            "$generation_dir/failure-manifest.env"
        failed_current_tmp="$output/scheduler/current.env.tmp.$$"
        {
            echo schema=simple-bootstrap-current-generation-v1
            echo generation="$generation"
            echo generation_dir="$generation_dir"
            echo lease_sha256="$(bootstrap_scheduler_hash_file "$lease")"
            echo status=failed
            echo failure_manifest="$generation_dir/failure-manifest.env"
        } >"$failed_current_tmp"
        bootstrap_scheduler_atomic_replace "$failed_current_tmp" \
            "$output/scheduler/current.env"
        echo "bootstrap-scheduler-error: Stage-4 continuation failed; log: $generation_dir/stage4-continuation.log" >&2
        exit 1
    fi
fi

if [ "$wants_full_cli" -eq 1 ]; then
    promotion_barrier_status=invalid
    policy_sha_now=absent
    [ ! -f "$root/.spipe/policy/vcs.sdn" ] ||
        policy_sha_now=$(bootstrap_scheduler_hash_file \
            "$root/.spipe/policy/vcs.sdn")
    actual_input_digest=$(input_digest)
    if [ "$policy_sha_now" = "$policy_sha" ] &&
       bootstrap_scheduler_verify_promotion_barrier \
        "$lease" "$generation" "$lease_sha" "$source_digest" \
        "$actual_input_digest" "$lineage" "$lineage_sha" "$output" \
        "$qualification_result" "$stage3_result" \
        "$generation_dir/stage4.result.env" &&
       bootstrap_stage3_verify_stage2_admission_receipt \
        "$qualification_admission" "$qualification_candidate" \
        "$admission_source" "$admission_runtime" "$admission_tool" \
        "$admission_args" "$admission_sanity" "$admission_receiver" "$root" &&
       bootstrap_stage3_verify_manifest "$stage3_manifest" "$root" \
        "$stage3_candidate"; then
        promotion_barrier_status=verified
    fi
    if [ "$promotion_barrier_status" != verified ]; then
        failure_reason=post-stage4-promotion-barrier-invalid
        bootstrap_scheduler_retire_generation "$generation_dir" "$output" \
            "$generation" "$lease" "$lease_sha" "$lineage" \
            "$lineage_sha" "$failure_reason" "$source_digest" \
            "$actual_input_digest" "$policy_sha" "$policy_sha_now" || exit 1
        echo 'bootstrap-scheduler-error: post-Stage4 promotion barrier failed; publication denied' >&2
        exit 1
    fi
fi

promotion_required=0
if [ "$wants_deploy" -eq 1 ]; then
    promotion_required=1
    promotion_tmp="$generation_dir/promotion-required.env.tmp.$$"
    {
        echo schema=simple-bootstrap-promotion-required-v1
        echo generation="$generation"
        echo status=blocked-pending-explicit-continuation
        echo lineage_path="$lineage"
        echo lineage_sha256="$lineage_sha"
        echo stage4_result_path="$generation_dir/stage4.result.env"
        echo stage4_result_sha256="$(bootstrap_scheduler_hash_file "$generation_dir/stage4.result.env")"
        echo requested_deploy=true
        echo requested_release="$wants_release"
        echo reason=automatic-publication-after-long-stage4-is-forbidden
    } >"$promotion_tmp"
    bootstrap_scheduler_atomic_replace "$promotion_tmp" \
        "$generation_dir/promotion-required.env"
fi

# Close the interval spent writing the promotion decision. A generation that
# became stale is never rewritten as qualified.
if [ "$wants_full_cli" -eq 1 ]; then
    final_policy_sha=absent
    [ ! -f "$root/.spipe/policy/vcs.sdn" ] ||
        final_policy_sha=$(bootstrap_scheduler_hash_file \
            "$root/.spipe/policy/vcs.sdn")
    final_input_digest=$(input_digest)
    if [ "$final_policy_sha" != "$policy_sha" ] ||
       ! bootstrap_scheduler_verify_promotion_barrier \
        "$lease" "$generation" "$lease_sha" "$source_digest" \
        "$final_input_digest" "$lineage" "$lineage_sha" "$output" \
        "$qualification_result" "$stage3_result" \
        "$generation_dir/stage4.result.env"; then
        bootstrap_scheduler_retire_generation "$generation_dir" "$output" \
            "$generation" "$lease" "$lease_sha" "$lineage" \
            "$lineage_sha" final-promotion-barrier-stale "$source_digest" \
            "$final_input_digest" "$policy_sha" "$final_policy_sha" || exit 1
        echo 'bootstrap-scheduler-error: generation became stale before qualification; trust state retired' >&2
        exit 1
    fi
fi

qualified_tmp="$lease.tmp.$$"
{
    echo schema=simple-bootstrap-generation-lease-v1
    echo generation="$generation"
    if [ "$promotion_required" -eq 1 ]; then
        echo status=qualified-awaiting-explicit-promotion
    else
        echo status=qualified
    fi
    echo previous_lease_sha256="$lease_sha"
    echo lineage_admission_sha256="$(bootstrap_scheduler_hash_file "$generation_dir/lineage-admission.env")"
    echo completed_epoch_seconds="$(date +%s)"
} >"$qualified_tmp"
bootstrap_scheduler_atomic_replace "$qualified_tmp" "$lease"
qualified_current_tmp="$output/scheduler/current.env.tmp.$$"
{
    echo schema=simple-bootstrap-current-generation-v1
    echo generation="$generation"
    echo generation_dir="$generation_dir"
    echo lease_sha256="$(bootstrap_scheduler_hash_file "$lease")"
    echo status=qualified
    echo lineage_admission="$generation_dir/lineage-admission.env"
} >"$qualified_current_tmp"
bootstrap_scheduler_atomic_replace "$qualified_current_tmp" \
    "$output/scheduler/current.env"
event generation-qualified lineage qualified
if [ "$promotion_required" -eq 1 ]; then
    echo "bootstrap-scheduler-error: Stage 4 is qualified and quarantined, but normal/full deploy and release fail closed until an explicit post-admitted promotion command is implemented; evidence: $generation_dir/promotion-required.env" >&2
    exit 78
fi
echo "bootstrap scheduler: PASS generation=$generation overlap=$overlap_observed schedule=$schedule_mode"
echo "bootstrap scheduler receipt: $generation_dir/lineage-admission.env"
