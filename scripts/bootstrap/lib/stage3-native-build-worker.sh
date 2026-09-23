#!/bin/sh
set -eu

# Internal worker for resume-stage3-from-admitted.sh.  The launcher runs this
# file in a dedicated systemd user-service cgroup so every descendant remains
# kernel-owned even after double-fork/reparenting.
[ "$#" -eq 25 ] || { echo 'stage3 worker: invalid argument count' >&2; exit 64; }
transcript=$1 root=$2 log=$3 worker_home=$4 worker_tmp=$5 worker_path=$6
admitted=$7 platform=$8 backend=$9
shift 9
threads=$1 timeout_seconds=$2 cache=$3 runtime=$4 candidate=$5 progress=$6
phase_profile=$7 memory_snapshot=$8 evidence_run_id=$9
shift 9
requested_route=$1 fallback_route=$2 process_max_kib=$3 mc_env=$4 cold_env=$5
diagnostic_env=$6
memory_high_mib=$7

BOOTSTRAP_STAGE3_FACADE_PATH="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT=$root
export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_VERSION_ROOT
. "$BOOTSTRAP_STAGE3_FACADE_PATH"

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

ulimit -v "$process_max_kib" || exit 125
timeout_args=
[ -z "$timeout_seconds" ] || timeout_args="--timeout $timeout_seconds"
bootstrap_stage3_run_transcribed "$transcript" "$root" "$log" \
  "$worker_home" "$worker_tmp" "$worker_path" RUST_LOG=error LIBRARY_PATH= \
  SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_STAGE3_STREAMING_SURFACES=1 \
  SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE="$requested_route" \
  SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE="$fallback_route" \
  SIMPLE_FRONTEND_CACHE=0 MALLOC_ARENA_MAX=2 MALLOC_TRIM_THRESHOLD_=0 \
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
  ${diagnostic_env} -- "$admitted" native-build --target "$platform" \
  --backend "$backend" --runtime-bundle core-c-bootstrap --threads "$threads" \
  ${timeout_args} --cache-dir "$cache" --mode dynload --runtime-path "$runtime" \
  -o "$candidate" src/app/cli/bootstrap_main.spl
