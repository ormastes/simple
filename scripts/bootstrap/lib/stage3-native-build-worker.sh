#!/bin/sh
set -eu

# Internal worker for resume-stage3-from-admitted.sh.  The launcher runs this
# file in a dedicated systemd user-service cgroup so every descendant remains
# kernel-owned even after double-fork/reparenting.
worker_arg_count=$#
[ "$#" -eq 28 ] || [ "$#" -eq 30 ] || [ "$#" -eq 31 ] || { echo 'stage3 worker: invalid argument count' >&2; exit 64; }
transcript=$1 root=$2 log=$3 worker_home=$4 worker_tmp=$5 worker_path=$6
admitted=$7 platform=$8 backend=$9
shift 9
threads=$1 timeout_seconds=$2 cache=$3 runtime=$4 candidate=$5 progress=$6
phase_profile=$7 memory_snapshot=$8 evidence_run_id=$9
shift 9
requested_route=$1 fallback_route=$2 process_max_kib=$3 mc_env=$4 cold_env=$5
diagnostic_env=$6
memory_high_mib=$7
abi_policy=$8 abi_receipt=$9 abi_receipt_sha=${10}
compiler_ceiling_env=${11:-}
compiler_cap=${12:-}

# The new positional value is the controller authority, including across a
# systemd manager that drops or supplies stale ambient environment. Legacy
# 28/30-argument callers retain only the historical host-platform default.
if [ "$worker_arg_count" -eq 31 ]; then
  observation_budget_ms=${13}
else
  observation_host=$(uname -s) || { echo 'stage3 worker: cannot identify observation host' >&2; exit 64; }
  case "$observation_host" in FreeBSD) observation_budget_ms=5000 ;; *) observation_budget_ms=1000 ;; esac
  [ "${SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS-$observation_budget_ms}" = "$observation_budget_ms" ] || {
    echo 'stage3 worker: unrecorded observation budget' >&2; exit 64;
  }
fi
case "$observation_budget_ms" in
  ''|0*|*[!0-9]*) echo 'stage3 worker: invalid observation budget' >&2; exit 64 ;;
esac
[ "${#observation_budget_ms}" -le 5 ] &&
  [ "$observation_budget_ms" -ge 1000 ] &&
  [ "$observation_budget_ms" -le 60000 ] || {
    echo 'stage3 worker: observation budget must be 1000..60000 ms' >&2; exit 64;
  }
SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS=$observation_budget_ms
export SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS

BOOTSTRAP_STAGE3_FACADE_PATH="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT=$root
export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_VERSION_ROOT
. "$BOOTSTRAP_STAGE3_FACADE_PATH"

# This optional transport is separate from the admitted parent's historical
# transcript. It belongs only to this newly hashed compiler invocation.
case "$compiler_ceiling_env" in
  '')
    [ "${SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB+x}" != x ] || {
      echo 'stage3 worker: unrecorded ambient compiler RSS ceiling' >&2; exit 64;
    } ;;
  SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB=*)
    compiler_ceiling=${compiler_ceiling_env#*=}
    bootstrap_stage3_compiler_ceiling_valid "$compiler_ceiling" &&
      bootstrap_stage3_compiler_ceiling_valid "$compiler_cap" &&
      [ "$compiler_cap" -le "$compiler_ceiling" ] &&
      [ "${SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB-$compiler_ceiling}" = "$compiler_ceiling" ] || {
      echo 'stage3 worker: invalid or conflicting compiler RSS ceiling' >&2; exit 64;
    }
    SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB=$compiler_ceiling
    [ "${SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB-$compiler_cap}" = "$compiler_cap" ] || {
      echo 'stage3 worker: conflicting compiler RSS cap' >&2; exit 64;
    }
    SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=$compiler_cap
    export SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB ;;
  *) echo 'stage3 worker: invalid compiler RSS ceiling binding' >&2; exit 64 ;;
esac
if [ -n "$compiler_cap" ]; then
  bootstrap_stage3_compiler_ceiling_valid "$compiler_cap" &&
    [ "${SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB-$compiler_cap}" = "$compiler_cap" ] || {
    echo 'stage3 worker: invalid or conflicting compiler RSS cap' >&2; exit 64;
  }
  SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=$compiler_cap
  export SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB
  # Re-admit the transported cap against this process's real current policy.
  # No ceiling variable is invented for an ordinary below-ceiling cap.
  [ "${SIMPLE_BOOTSTRAP_RSS_CAP_MODE:-enforce}" = enforce ] &&
    [ -z "${BOOTSTRAP_TREE_RSS_MEMINFO_PATH+x}" ] &&
    [ -z "${BOOTSTRAP_TREE_RSS_TEST_FIXTURE+x}" ] &&
    [ -z "${SIMPLE_PROCESS_TREE_RSS_MEMINFO_PATH+x}" ] &&
    [ -z "${SIMPLE_PROCESS_TREE_RSS_TEST_FIXTURE+x}" ] || {
    echo 'stage3 worker: explicit compiler cap requires enforced real policy' >&2; exit 64;
  }
  . "$root/scripts/bootstrap/lib/tree-rss-policy.shs"
  bootstrap_tree_rss_resolve "$threads" "$root" &&
    [ "$bootstrap_tree_rss_cap_kib" = "$compiler_cap" ] || {
    echo "stage3 worker: compiler RSS cap policy refused: ${bootstrap_tree_rss_refusal:-mismatch}" >&2; exit 64;
  }
elif [ "${SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB+x}" = x ]; then
  # Historical Darwin launches install this exact enclosing default after
  # hashing their old vector. A user-requested cap is transported nonempty
  # above, even when its value happens to equal this legacy default.
  case "$platform:$(uname -s):$SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB" in
    *-apple-darwin:Darwin:6835937) ;;
    *) echo 'stage3 worker: unrecorded ambient compiler RSS cap' >&2; exit 64 ;;
  esac
fi

# The caller fully verified admission. Refuse a missing or changed transfer
# before env-i can erase its policy, or before the compiler can use its bytes.
stage3_abi_transfer_error() {
  echo 'stage3 worker: verified ABI admission transfer is absent or changed' >&2
  exit 64
}
[ -f "$admitted" ] && [ ! -L "$admitted" ] || stage3_abi_transfer_error
abi_producer_sha=$(bootstrap_stage3_hash_file "$admitted") || stage3_abi_transfer_error
[ "${#abi_receipt_sha}" -eq 64 ] && [ "${#abi_producer_sha}" -eq 64 ] || stage3_abi_transfer_error
case "$abi_receipt_sha$abi_producer_sha" in *[!0-9a-f]*) stage3_abi_transfer_error ;; esac
[ "$abi_policy" = v1 ] && bootstrap_stage3_normalized_absolute "$abi_receipt" &&
  [ -f "$abi_receipt" ] && [ ! -L "$abi_receipt" ] &&
  [ "$(bootstrap_stage3_hash_file "$abi_receipt")" = "$abi_receipt_sha" ] &&
  [ "$(bootstrap_stage3_manifest_value schema "$abi_receipt")" = simple-bootstrap-stage2-admission-v2 ] &&
  [ "$(bootstrap_stage3_manifest_value status "$abi_receipt")" = admitted ] &&
  [ "$(bootstrap_stage3_manifest_value simple_abi_policy "$abi_receipt")" = "$abi_policy" ] &&
  [ "$(bootstrap_stage3_manifest_value candidate_sha256 "$abi_receipt")" = "$abi_producer_sha" ] || stage3_abi_transfer_error

# On Linux, prove the memory controller limits are effective inside this worker
# before the compiler can allocate. Other platforms retain the portable ulimit
# below and never enter the Linux cgroup launcher branch.
case "$platform" in
  *-linux-*)
    cgroup_path=$(awk -F: '$1 == "0" { print $3; exit }' /proc/self/cgroup) || exit 125
    [ -n "$cgroup_path" ] || exit 125
    cgroup_root="/sys/fs/cgroup${cgroup_path}"
    [ -r "$cgroup_root/memory.high" ] && [ -r "$cgroup_root/memory.max" ] || exit 125
    actual_high=$(sed -n '1p' "$cgroup_root/memory.high") || exit 125
    actual_max=$(sed -n '1p' "$cgroup_root/memory.max") || exit 125
    expected_high=$((memory_high_mib * 1024 * 1024))
    expected_max=$(((process_max_kib / 1024) * 1024 * 1024))
    [ "$actual_high" = "$expected_high" ] && [ "$actual_max" = "$expected_max" ] || {
      echo "stage3 worker: cgroup memory limits ineffective (high=$actual_high max=$actual_max)" >&2
      exit 125
    }
    ;;
esac

case "$platform" in
  # Darwin rejects RLIMIT_AS (`ulimit -v`: Invalid argument). The resume
  # launcher runs this worker under process-tree-rss-watchdog.pl with the same
  # per-process maximum instead, so the cap is enforced, not dropped.
  *-apple-darwin*) ;;
  *) ulimit -v "$process_max_kib" || exit 125 ;;
esac
timeout_args=
[ -z "$timeout_seconds" ] || timeout_args="--timeout $timeout_seconds"
bootstrap_stage3_run_transcribed "$transcript" "$root" "$log" \
  "$worker_home" "$worker_tmp" "$worker_path" RUST_LOG=error LIBRARY_PATH= \
  SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent SIMPLE_BOOTSTRAP=1 \
  SIMPLE_ABI_POLICY="$abi_policy" SIMPLE_ABI_ADMISSION_RECEIPT="$abi_receipt" \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_STAGE3_STREAMING_SURFACES=0 \
  SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE="$requested_route" \
  SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE="$fallback_route" \
  SIMPLE_FRONTEND_CACHE=1 SIMPLE_FRONTEND_CACHE_DIR="$cache/frontend" \
  SIMPLE_HIR_CACHE=1 SIMPLE_HIR_CACHE_DIR="$cache/hir" \
  MALLOC_ARENA_MAX=2 MALLOC_TRIM_THRESHOLD_=0 \
  SIMPLE_NATIVE_ARENA_DECLS=1 SIMPLE_NO_STUB_FALLBACK=1 \
  SIMPLE_PACKAGE_INDEX_COLD_INIT=1 ${mc_env} ${cold_env} \
  SIMPLE_BUILD_PROGRESS_EVENTS="$progress" SIMPLE_COMPILER_PHASE_PROFILE=1 \
  SIMPLE_COMPILER_PHASE_PROFILE_FILE="$phase_profile" \
  SIMPLE_MEM_SNAPSHOT_FILE="$memory_snapshot" \
  SIMPLE_EVIDENCE_RUN_ID="$evidence_run_id" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NATIVE_BUILD_TARGET="$platform" SIMPLE_NATIVE_BUILD_THREADS="$threads" \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$cache" SIMPLE_RUNTIME_PATH="$runtime" \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap SIMPLE_BINARY="$admitted" \
  ${diagnostic_env} ${compiler_ceiling_env:+"$compiler_ceiling_env"} \
  ${compiler_cap:+"SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=$compiler_cap"} -- "$admitted" native-build --target "$platform" \
  --backend "$backend" --runtime-bundle core-c-bootstrap --threads "$threads" \
  ${timeout_args} --cache-dir "$cache" --mode dynload --runtime-path "$runtime" \
  -o "$candidate" src/app/cli/bootstrap_main.spl
