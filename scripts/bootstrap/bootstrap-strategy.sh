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
if [ "${SIMPLE_BOOTSTRAP_SCHEDULER_SELFTEST:-0}" = 1 ]; then
    engine=${SIMPLE_BOOTSTRAP_SCHEDULER_ENGINE:-$engine}
    qualifier=${SIMPLE_BOOTSTRAP_SCHEDULER_QUALIFIER:-$qualifier}
elif [ -n "${SIMPLE_BOOTSTRAP_SCHEDULER_ENGINE:-}" ] ||
     [ -n "${SIMPLE_BOOTSTRAP_SCHEDULER_QUALIFIER:-}" ]; then
    echo 'bootstrap-scheduler-error: task overrides are self-test-only' >&2
    exit 2
fi
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
qualification_memory=${SIMPLE_BOOTSTRAP_QUALIFICATION_MEMORY_MIB:-1024}
critical_memory=${SIMPLE_BOOTSTRAP_CRITICAL_MEMORY_MIB:-1024}
case "$qualification_memory:$critical_memory" in
    *[!0-9:]*|0:*|*:0) echo 'bootstrap-scheduler-error: invalid memory reservation' >&2; exit 2 ;;
esac
schedule_mode=speculative
if [ "$qualification_cpu" -eq 0 ] ||
   [ "$memory_total" -lt $((qualification_memory + critical_memory)) ]; then
    schedule_mode=serialized-resource-guard
    qualification_cpu=1
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
    SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1 \
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
    SIMPLE_BOOTSTRAP_QUALIFICATION_CPU_SLOTS="$qualification_cpu" \
        /bin/sh "$qualifier" "$output" "$generation_dir" "$lease" \
        "$lease_sha" "$engine_done" \
        >"$generation_dir/qualification.log" 2>&1
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
        # Production stage engines own a native process group. Test fixtures do
        # not, so keep the destructive scope exact in self-test mode.
        if [ "${SIMPLE_BOOTSTRAP_SCHEDULER_SELFTEST:-0}" = 1 ]; then
            kill "$engine_pid" 2>/dev/null || true
        else
            kill -TERM "-$engine_pid" 2>/dev/null || kill "$engine_pid" 2>/dev/null || true
        fi
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
    continuation_env=SIMPLE_BOOTSTRAP_STAGE4_QUARANTINE=1
    if [ "$wants_deploy" -eq 1 ]; then
        set -- "$@" --deploy
        continuation_env=SIMPLE_BOOTSTRAP_SCHEDULER_RELEASE_ADMITTED=1
    fi
    [ "$wants_release" -eq 0 ] || set -- "$@" --release
    set +e
    env SIMPLE_BOOTSTRAP_STRATEGY_SUPERVISED=1 \
        "$continuation_env" \
        /bin/sh "$engine" "$@" \
        >"$generation_dir/stage4-continuation.log" 2>&1
    continuation_rc=$?
    set -e
    continuation_finished=$(date +%s)
    if [ "$continuation_rc" -eq 0 ]; then
        continuation_status=passed
    fi
    continuation_output_class=quarantined
    [ "$wants_deploy" -eq 0 ] || continuation_output_class=protected-publication
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
        echo "bootstrap-scheduler-error: Stage-4 continuation failed; log: $generation_dir/stage4-continuation.log" >&2
        exit 1
    fi
fi

lineage_tmp="$generation_dir/lineage-admission.env.tmp.$$"
{
    echo schema=simple-bootstrap-lineage-admission-v1
    echo generation="$generation"
    echo status=qualified
    echo lease_sha256="$lease_sha"
    echo graph_sha256="$runtime_graph_sha"
    echo source_generation_sha256="$source_digest"
    echo stage_engine_receipt_sha256="$(bootstrap_scheduler_hash_file "$generation_dir/tasks/stage-engine.env")"
    echo stage2_qualification_receipt_sha256="$(bootstrap_scheduler_hash_file "$generation_dir/tasks/stage2-qualification.env")"
    echo continuation_status="$continuation_status"
    echo overlap_observed="$overlap_observed"
    echo schedule_mode="$schedule_mode"
    echo ancestor_chain=qualified-untainted
    echo completed_epoch_seconds="$(date +%s)"
} >"$lineage_tmp"
bootstrap_scheduler_atomic_replace "$lineage_tmp" \
    "$generation_dir/lineage-admission.env"

qualified_tmp="$lease.tmp.$$"
{
    echo schema=simple-bootstrap-generation-lease-v1
    echo generation="$generation"
    echo status=qualified
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
echo "bootstrap scheduler: PASS generation=$generation overlap=$overlap_observed schedule=$schedule_mode"
echo "bootstrap scheduler receipt: $generation_dir/lineage-admission.env"
