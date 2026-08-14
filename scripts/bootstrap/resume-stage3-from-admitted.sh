#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)
source_output=${1:?usage: resume-stage3-from-admitted.sh OUTPUT_DIR}
case "$source_output" in /*|*../*|../*|*/..|..) exit 2 ;; esac
output="$root/$source_output"
[ "$(CDPATH= cd -- "$output" && pwd -P)" = "$output" ] || exit 1

BOOTSTRAP_STAGE3_FACADE_PATH="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
export BOOTSTRAP_STAGE3_FACADE_PATH
. "$BOOTSTRAP_STAGE3_FACADE_PATH"
. "$root/scripts/check/lib/bootstrap-planner-admission-bound.shs"
planner_admission=${SIMPLE_BOOTSTRAP_REASON_RECEIPT:-}
[ -n "$planner_admission" ] || {
  echo "bootstrap-policy-error: planner-admission-v2-required" >&2; exit 64;
}
bootstrap_planner_v2_verify "$planner_admission" "$root" || exit 64
[ "$(bootstrap_planner_v2_field target "$planner_admission")" = \
  //bootstrap:stage3 ] || exit 64

platform=$(bootstrap_stage3_host_platform)
stage3="$output/stage3/$platform"
stage2="$output/stage2/$platform/simple"
admitted="$stage3/stage2-admitted/simple"
runtime="$stage3/stage2-runtime-authority"
seed="$runtime/simple"
stamp="$seed.inputs.sha256"
native_all="$runtime/libsimple_native_all.a"
backfill="$runtime/libsimple_compiler_backfill.a"
stage2_sanity="$stage3/stage2-sanity.env"
stage2_transcript="$stage3/stage2-command.transcript"
stage2_log="$output/logs/$platform/stage2-native-build.log"
candidate="$stage3/simple"
manifest="$stage3/provenance.env"
stage3_transcript="$stage3/stage3-command.transcript"
stage3_log="$output/logs/$platform/stage3-native-build.log"
stage3_sanity="$stage3/stage3-sanity.env"
stage2_cache="$stage3/stage2-native-cache"
stage3_cache="$stage3/stage3-native-cache"
home="$stage3/stage3-home"
tmp="$stage3/stage3-tmp"
source_before="$stage3/source-inputs-before.txt"
source_after="$stage3/source-inputs-after.txt"
git_before="$stage3/git-state-before.env"
git_after="$stage3/git-state-after.env"
tool_before="$stage3/tool-authority-before.txt"
tool_after="$stage3/tool-authority-after.txt"
runtime_origin_before="$stage3/runtime-origin-before.txt"
runtime_origin_after="$stage3/runtime-origin-after.txt"
runtime_admitted="$stage3/runtime-admitted.txt"
lock="$output.lock"
archive="$stage3/recovery-threads1"

for required in "$stage2" "$admitted" "$seed" "$stamp" "$native_all" \
  "$stage2_sanity" "$stage2_transcript" "$stage2_log" "$source_before" \
  "$runtime_origin_before" "$runtime_origin_after" "$runtime_admitted" \
  "$tool_before"; do
  [ -f "$required" ] && [ ! -L "$required" ] || exit 1
  [ "$(bootstrap_stage3_canonical_file "$required")" = "$required" ] || exit 1
done
for required_dir in "$runtime" "$stage2_cache"; do
  [ -d "$required_dir" ] && [ ! -L "$required_dir" ] || exit 1
  [ "$(bootstrap_stage3_canonical_path "$required_dir")" = "$required_dir" ] || exit 1
done

stage2_sha=$(bootstrap_stage3_hash_file "$stage2")
admitted_sha=$(bootstrap_stage3_hash_file "$admitted")
[ "$stage2_sha" = "$admitted_sha" ] || exit 1
[ "$(bootstrap_stage3_manifest_value status "$stage2_sanity")" = pass ] || exit 1
[ "$(bootstrap_stage3_manifest_value candidate_sha256_after "$stage2_sanity")" = "$admitted_sha" ] || exit 1
bootstrap_stage3_verify_sanity_evidence "$stage2_sanity" "$stage2" "$root" \
  cranelift "$(bootstrap_stage3_transcript_host_value "$stage2_transcript" HOME)" \
  "$(bootstrap_stage3_transcript_host_value "$stage2_transcript" TMPDIR)" \
  "$(bootstrap_stage3_transcript_host_value "$stage2_transcript" PATH)"
path=$(bootstrap_stage3_transcript_host_value "$stage2_transcript" PATH)
cmp -s "$runtime_origin_before" "$runtime_origin_after"
cmp -s "$runtime_origin_after" "$runtime_admitted"
runtime_check="$archive/runtime-preflight.$$"
mkdir -p "$archive"
bootstrap_stage3_directory_snapshot "$runtime_check" "$runtime"
cmp -s "$runtime_admitted" "$runtime_check"
rm -f "$runtime_check"

if [ -f "$manifest" ] && bootstrap_stage3_verify_manifest "$manifest" "$root" "$candidate" >/dev/null 2>&1; then
  echo "error: canonical Stage 3 already converged: $manifest" >&2
  exit 1
fi
mkdir "$lock" || { echo "error: bootstrap output is locked: $lock" >&2; exit 1; }
printf '%s\n' "$$" >"$lock/pid"
trap 'rm -rf "$lock"' EXIT HUP INT TERM

# Prune native-build cache scope directories older than a TTL.
#
# Scope dirs are named
# `backend=...;cpu=...;opt=...;compiler=<sha>+src<fingerprint>n<count>` and are
# mint-once: as soon as any input in the closure changes, the source
# fingerprint changes and a NEW scope dir is minted. The old one is never
# consulted again, and nothing else ever collects it. That was harmless only
# while the wrappers wiped the entire cache dir on every run; now that these
# caches persist across runs (so an unchanged tree gets a real cache hit) the
# wipe is gone and scope dirs would otherwise accumulate without bound.
#
# Age-based rather than LRU on purpose: it needs no bookkeeping sidecar and no
# lock protocol. Several bootstrap lanes build concurrently on this host, and a
# scope dir whose mtime is older than the TTL cannot belong to a live build, so
# this can never pull artifacts out from under a running lane. Only entries
# matching the `backend=*` scope-dir shape are ever removed, so sibling files
# (build_cache.sdn, *.smf) are untouched. Override the window with
# BOOTSTRAP_NATIVE_CACHE_TTL_DAYS; 0 or a non-numeric value disables pruning.
bootstrap_native_cache_prune() {
  bnc_dir=$1
  bnc_ttl=${BOOTSTRAP_NATIVE_CACHE_TTL_DAYS:-7}
  [ -d "${bnc_dir}" ] || return 0
  case "${bnc_ttl}" in
    ''|*[!0-9]*) return 0 ;;
  esac
  [ "${bnc_ttl}" -gt 0 ] || return 0
  bnc_n=$(find "${bnc_dir}" -maxdepth 1 -type d -name 'backend=*' \
    -mtime +"${bnc_ttl}" -print 2>/dev/null | wc -l)
  [ "${bnc_n}" -gt 0 ] || return 0
  find "${bnc_dir}" -maxdepth 1 -type d -name 'backend=*' \
    -mtime +"${bnc_ttl}" -exec rm -rf {} + 2>/dev/null || true
  echo "  native cache: pruned ${bnc_n} scope dir(s) older than ${bnc_ttl}d in ${bnc_dir}"
}

for old in "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_sanity" "$manifest"; do
  if [ -e "$old" ]; then cp -p "$old" "$archive/$(basename "$old").before-resume"; fi
done
rm -f "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_sanity" "$manifest"
# stage3-native-cache is content-hash scoped by the pure-Simple driver itself
# (driver_native_sources_fingerprint in
# src/compiler/80.driver/driver_aot_native_output.spl), so a resumed run with
# an unchanged source tree can reuse it. Wiping it unconditionally on every
# resume defeated cross-run incrementality. Preserve by default;
# RESUME_STAGE3_FRESH_CACHE=1 forces a clean rebuild.
if [ "${RESUME_STAGE3_FRESH_CACHE:-0}" = 1 ]; then
  rm -rf "$stage3_cache"
else
  # Preserved cache still needs a reaper: scope dirs are mint-once and nothing
  # else collects them now that the unconditional wipe is gone.
  bootstrap_native_cache_prune "$stage3_cache"
  bootstrap_native_cache_prune "$stage2_cache"
fi
mkdir -p "$stage3_cache" "$home" "$tmp" "$(dirname "$stage3_log")"

# Recovery starts a fresh evidence interval after the immutable Stage-2 checks.
bootstrap_stage3_source_snapshot "$source_before" "$root"
bootstrap_stage3_git_state "$root" "$git_before"
bootstrap_stage3_tool_authority_snapshot "$tool_before" "$path" "$root"
script="$root/scripts/bootstrap/bootstrap-from-scratch.sh"
helper="$BOOTSTRAP_STAGE3_FACADE_PATH"
script_sha_before=$(bootstrap_stage3_hash_file "$script")
helper_sha_before=$(bootstrap_stage3_hash_file "$helper")
helper_bundle_before=$(bootstrap_stage3_helper_bundle_fingerprint)
seed_fingerprint=$(bootstrap_stage3_manifest_value inputs_fingerprint "$stamp")
progress="$output/bootstrap-build-progress.events"
memory_snapshot="$stage3/memory-snapshot-v1.$$.events"
phase_profile="$stage3/phase-profile.$$.events"
evidence_run_id="stage3-${platform}-$$"
[ ! -e "$memory_snapshot" ] && [ ! -L "$memory_snapshot" ] || exit 1
[ ! -e "$phase_profile" ] && [ ! -L "$phase_profile" ] || exit 1

stage2_threads=$(sed -n '/^argv:[0-9][0-9]*:--threads$/{n;s/^argv:[0-9][0-9]*://p;q;}' "$stage2_transcript")
case "$stage2_threads" in ''|*[!0-9]*) exit 1 ;; esac
stage2_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_NATIVE_BUILD_RUST=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$progress" "SIMPLE_BINARY=$seed" \
  native-build --target "$platform" --backend cranelift \
  --runtime-bundle core-c-bootstrap --source src/compiler --source src/app \
  --source src/lib --entry-closure --threads "$stage2_threads" \
  --cache-dir "$stage2_cache" --mode dynload --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$runtime" -o "$stage2")
stage3_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_STAGE3_STREAMING_SURFACES=1" \
  "MALLOC_ARENA_MAX=2" "MALLOC_TRIM_THRESHOLD_=0" \
  "SIMPLE_NATIVE_ARENA_DECLS=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$progress" \
  "SIMPLE_COMPILER_PHASE_PROFILE=1" \
  "SIMPLE_COMPILER_PHASE_PROFILE_FILE=$phase_profile" \
  "SIMPLE_MEM_SNAPSHOT_FILE=$memory_snapshot" \
  "SIMPLE_EVIDENCE_RUN_ID=$evidence_run_id" \
  "LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1" \
  "SIMPLE_NATIVE_BUILD_TARGET=$platform" "SIMPLE_NATIVE_BUILD_THREADS=1" \
  "SIMPLE_NATIVE_BUILD_CACHE_DIR=$stage3_cache" "SIMPLE_RUNTIME_PATH=$runtime" \
  "SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap" "SIMPLE_BINARY=$admitted" \
  native-build --target "$platform" --backend cranelift \
  --runtime-bundle core-c-bootstrap --threads 1 --cache-dir "$stage3_cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl)

set +e
bootstrap_stage3_run_transcribed "$stage3_transcript" "$root" "$stage3_log" \
  "$home" "$tmp" "$path" RUST_LOG=error LIBRARY_PATH= \
  SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_STAGE3_STREAMING_SURFACES=1 \
  MALLOC_ARENA_MAX=2 MALLOC_TRIM_THRESHOLD_=0 SIMPLE_NATIVE_ARENA_DECLS=1 \
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BUILD_PROGRESS_EVENTS="$progress" \
  SIMPLE_COMPILER_PHASE_PROFILE=1 \
  SIMPLE_COMPILER_PHASE_PROFILE_FILE="$phase_profile" \
  SIMPLE_MEM_SNAPSHOT_FILE="$memory_snapshot" \
  SIMPLE_EVIDENCE_RUN_ID="$evidence_run_id" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NATIVE_BUILD_TARGET="$platform" SIMPLE_NATIVE_BUILD_THREADS=1 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$stage3_cache" SIMPLE_RUNTIME_PATH="$runtime" \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap SIMPLE_BINARY="$admitted" -- \
  "$admitted" native-build --target "$platform" --backend cranelift \
  --runtime-bundle core-c-bootstrap --threads 1 --cache-dir "$stage3_cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl
status=$?
set -e
if [ "$status" -ne 0 ]; then
  exit "$status"
fi
[ -x "$candidate" ] || {
  echo "error: Stage 3 compiler exited successfully without an executable candidate" >&2
  exit 1
}
! grep -qE '^(Build complete: [0-9]+ compiled|Linked: .* via clang)' "$stage3_log" || exit 1
[ "$(bootstrap_stage3_hash_file "$admitted")" = "$admitted_sha" ] || exit 1
runtime_check="$archive/runtime-after.$$"
bootstrap_stage3_directory_snapshot "$runtime_check" "$runtime"
cmp -s "$runtime_admitted" "$runtime_check"
rm -f "$runtime_check"

CANDIDATE_FRONTEND_ROOT=$root
COMPILER_PROBE_TIMEOUT_SECONDS=5
COMPILER_BUILD_TIMEOUT_SECONDS=60
COMPILER_EXEC_TIMEOUT_SECONDS=5
COMPILER_CHECK_KILL_GRACE_SECONDS=1
. "$root/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs"
bootstrap_stage_sanity() (
  candidate_sanity=$1 evidence=$2 sanity_home=$3 sanity_tmp=$4 sanity_path=$5
  for name in $(env | sed 's/=.*//'); do unset "$name"; done
  HOME=$sanity_home TMPDIR=$sanity_tmp PATH=$sanity_path LC_ALL=C LANG=C
  export HOME TMPDIR PATH LC_ALL LANG
  evidence_tmp="$evidence.tmp.$$" frontend_log="$evidence_tmp.frontend"
  before=$(bootstrap_stage3_hash_file "$candidate_sanity")
  version_status=0; version=$(run_timeout 10 "$candidate_sanity" --version 2>&1) || version_status=$?
  unsupported_status=0
  unsupported=$(run_timeout 10 "$candidate_sanity" run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl 2>&1) || unsupported_status=$?
  frontend_status=0
  CANDIDATE_FRONTEND_BACKEND=cranelift candidate_frontend_smoke "$candidate_sanity" >"$frontend_log" 2>&1 || frontend_status=$?
  after=$(bootstrap_stage3_hash_file "$candidate_sanity")
  sanity_status=fail
  if [ "$version_status" -eq 0 ] && [ "$version" = "simple-bootstrap 1.0.0-beta" ] && \
    [ "$unsupported_status" -eq 1 ] && case "$unsupported" in *"unknown command 'run'"*) true;; *) false;; esac && \
    [ "$frontend_status" -eq 0 ] && [ "$before" = "$after" ]; then sanity_status=pass; fi
  { echo schema=simple-bootstrap-sanity-evidence-v1; echo status="$sanity_status"; \
    echo candidate_sha256_before="$before"; echo version_status="$version_status"; \
    echo version_output="$version"; echo unsupported_status="$unsupported_status"; \
    printf 'unsupported_output_sha256=%s\n' "$(printf %s "$unsupported" | bootstrap_stage3_hash_stream)"; \
    echo frontend_smoke_status="$frontend_status"; \
    echo frontend_smoke_output_sha256="$(bootstrap_stage3_hash_file "$frontend_log")"; \
    echo candidate_sha256_after="$after"; } >"$evidence_tmp"
  mv "$evidence_tmp" "$evidence"; rm -f "$frontend_log"; [ "$sanity_status" = pass ]
)
bootstrap_stage_sanity "$candidate" "$stage3_sanity" "$home" "$tmp" "$path"
bootstrap_stage3_source_snapshot "$source_after" "$root"
bootstrap_stage3_git_state "$root" "$git_after"
bootstrap_stage3_tool_authority_snapshot "$tool_after" "$path" "$root"
cmp -s "$source_before" "$source_after"
cmp -s "$git_before" "$git_after"
cmp -s "$tool_before" "$tool_after"

BSTAGE3_ROOT=$root BSTAGE3_MANIFEST=$manifest BSTAGE3_PLATFORM=$platform
BSTAGE3_BACKEND=cranelift BSTAGE3_MODE=dynload BSTAGE3_SEED=$seed
BSTAGE3_SEED_STAMP=$stamp BSTAGE3_NATIVE_ALL=$native_all BSTAGE3_BACKFILL=$backfill
BSTAGE3_RUNTIME_ORIGIN_BEFORE=$runtime_origin_before BSTAGE3_RUNTIME_ORIGIN_AFTER=$runtime_origin_after
BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT=$runtime_admitted BSTAGE3_TOOL_AUTHORITY=$tool_after
BSTAGE3_STAGE2=$stage2 BSTAGE3_STAGE2_ADMITTED=$admitted BSTAGE3_STAGE3=$candidate
BSTAGE3_SOURCE_BEFORE=$source_before BSTAGE3_SOURCE_AFTER=$source_after
BSTAGE3_STAGE2_LOG=$stage2_log BSTAGE3_STAGE3_LOG=$stage3_log
BSTAGE3_STAGE2_ARGS_SHA256=$stage2_args BSTAGE3_STAGE3_ARGS_SHA256=$stage3_args
BSTAGE3_STAGE2_THREADS=$stage2_threads BSTAGE3_STAGE3_THREADS=1
BSTAGE3_STAGE2_CACHE_DIR=$stage2_cache BSTAGE3_STAGE3_CACHE_DIR=$stage3_cache
BSTAGE3_RUNTIME_PATH=$runtime BSTAGE3_STAGE2_COMMAND_OUTPUT=$stage2
BSTAGE3_STAGE3_COMMAND_OUTPUT=$candidate BSTAGE3_BOOTSTRAP_SCRIPT=$script
BSTAGE3_HELPER=$helper BSTAGE3_HELPER_SHA256_BEFORE=$helper_sha_before
BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE=$helper_bundle_before
BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE=$script_sha_before
BSTAGE3_SEED_INPUTS_FINGERPRINT=$seed_fingerprint BSTAGE3_SEED_FEATURES=
BSTAGE3_GIT_BEFORE=$git_before BSTAGE3_GIT_AFTER=$git_after
BSTAGE3_STAGE2_TRANSCRIPT=$stage2_transcript BSTAGE3_STAGE3_TRANSCRIPT=$stage3_transcript
BSTAGE3_STAGE2_SANITY=$stage2_sanity BSTAGE3_STAGE3_SANITY=$stage3_sanity
BSTAGE3_LOCK=$lock BSTAGE3_RUST_LOG=error
export BSTAGE3_ROOT BSTAGE3_MANIFEST BSTAGE3_PLATFORM BSTAGE3_BACKEND BSTAGE3_MODE \
  BSTAGE3_SEED BSTAGE3_SEED_STAMP BSTAGE3_NATIVE_ALL BSTAGE3_BACKFILL \
  BSTAGE3_RUNTIME_ORIGIN_BEFORE BSTAGE3_RUNTIME_ORIGIN_AFTER \
  BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT BSTAGE3_TOOL_AUTHORITY BSTAGE3_STAGE2 \
  BSTAGE3_STAGE2_ADMITTED BSTAGE3_STAGE3 BSTAGE3_SOURCE_BEFORE BSTAGE3_SOURCE_AFTER \
  BSTAGE3_STAGE2_LOG BSTAGE3_STAGE3_LOG BSTAGE3_STAGE2_ARGS_SHA256 \
  BSTAGE3_STAGE3_ARGS_SHA256 BSTAGE3_STAGE2_THREADS BSTAGE3_STAGE3_THREADS \
  BSTAGE3_STAGE2_CACHE_DIR BSTAGE3_STAGE3_CACHE_DIR BSTAGE3_RUNTIME_PATH \
  BSTAGE3_STAGE2_COMMAND_OUTPUT BSTAGE3_STAGE3_COMMAND_OUTPUT BSTAGE3_BOOTSTRAP_SCRIPT \
  BSTAGE3_HELPER BSTAGE3_HELPER_SHA256_BEFORE BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE \
  BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE BSTAGE3_SEED_INPUTS_FINGERPRINT \
  BSTAGE3_SEED_FEATURES BSTAGE3_GIT_BEFORE BSTAGE3_GIT_AFTER \
  BSTAGE3_STAGE2_TRANSCRIPT BSTAGE3_STAGE3_TRANSCRIPT BSTAGE3_STAGE2_SANITY \
  BSTAGE3_STAGE3_SANITY BSTAGE3_LOCK BSTAGE3_RUST_LOG
bootstrap_stage3_write_manifest
bootstrap_stage3_verify_manifest "$manifest" "$root" "$candidate"
