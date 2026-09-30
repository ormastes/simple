#!/bin/sh
set -eu

# Exit 2 means "ERROR — nothing was checked" and MUST always state the reason.
# A silent exit 2 here made a real Stage-2 refusal UNDIAGNOSABLE — see
# doc/08_tracking/bug/simpleos_stage2_bootstrap_sanity_exit2_without_diagnostic_2026-08-20.md
bootstrap_stage3_error() {
  printf 'ERROR — nothing was checked (%s)\n' "$1" >&2
  exit 2
}

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)
source_output=${1:?usage: resume-stage3-from-admitted.sh OUTPUT_DIR}
case "$source_output" in /*|*../*|../*|*/..|..) bootstrap_stage3_error "OUTPUT_DIR must be a repo-relative path without .. components: $source_output" ;; esac
output="$root/$source_output"
[ "$(CDPATH= cd -- "$output" && pwd -P)" = "$output" ] ||
  bootstrap_stage3_error "OUTPUT_DIR is not a canonical existing directory: $output"

BOOTSTRAP_STAGE3_FACADE_PATH="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
BOOTSTRAP_STAGE3_VERSION_ROOT=$root
export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_VERSION_ROOT
. "$BOOTSTRAP_STAGE3_FACADE_PATH"
. "$root/scripts/bootstrap/bootstrap-cache-release-vector.shs"
. "$root/scripts/bootstrap/bootstrap-cache-lineage.shs"
BOOTSTRAP_CACHE_PROCESS_HELPER_PATH="$root/scripts/check/lib/portable-hardlink-lock.pl"
. "$root/scripts/check/lib/bootstrap-planner-admission-bound.shs"
planner_admission=${SIMPLE_BOOTSTRAP_REASON_RECEIPT:-}
[ -n "$planner_admission" ] || {
  echo "bootstrap-policy-error: planner-admission-v2-required" >&2; exit 64;
}
bootstrap_planner_v2_verify "$planner_admission" "$root" || exit 64
[ "$(bootstrap_planner_v2_field target "$planner_admission")" = \
  //bootstrap:stage3 ] || exit 64

platform=$(bootstrap_stage3_host_platform)
exe_suffix=
archive_prefix=lib
archive_suffix=.a
case "$platform" in
  *-pc-windows-msvc) exe_suffix=.exe; archive_prefix=; archive_suffix=.lib ;;
  *-pc-windows-gnu) exe_suffix=.exe ;;
esac
stage3="$output/stage3/$platform"
stage2="$output/stage2/$platform/simple$exe_suffix"
admitted="$stage3/stage2-admitted/simple$exe_suffix"
stage2_admission="$stage3/stage2-admitted/admission.env"
runtime="$stage3/stage2-runtime-authority"
seed="$runtime/simple$exe_suffix"
stamp="$seed.inputs.sha256"
native_all="$runtime/${archive_prefix}simple_native_all${archive_suffix}"
backfill="$runtime/${archive_prefix}simple_compiler_backfill${archive_suffix}"
stage2_sanity="$stage3/stage2-sanity.env"
stage2_receiver="$stage3/stage2-receiver.env"
stage2_receiver_log="$stage3/stage2-receiver.log"
stage2_transcript="$stage3/stage2-command.transcript"
stage2_log="$output/logs/$platform/stage2-native-build.log"
candidate="$stage3/simple$exe_suffix"
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
archive="$stage3/attempts/recovery-threads1-$(date -u '+%Y%m%dT%H%M%S')-$$"

for required in "$stage2" "$admitted" "$stage2_admission" "$seed" "$stamp" "$native_all" \
  "$stage2_sanity" "$stage2_receiver" "$stage2_receiver_log" \
  "$stage2_transcript" "$stage2_log" "$source_before" \
  "$git_before" \
  "$runtime_origin_before" "$runtime_origin_after" "$runtime_admitted" \
  "$tool_before"; do
  { [ -f "$required" ] && [ ! -L "$required" ]; } ||
    bootstrap_stage3_error "required Stage-2 input missing or is a symlink: $required"
  [ "$(bootstrap_stage3_canonical_file "$required")" = "$required" ] ||
    bootstrap_stage3_error "required Stage-2 input is not a canonical path: $required"
done
for required_dir in "$runtime" "$stage2_cache"; do
  { [ -d "$required_dir" ] && [ ! -L "$required_dir" ]; } ||
    bootstrap_stage3_error "required Stage-2 directory missing or is a symlink: $required_dir"
  [ "$(bootstrap_stage3_canonical_path "$required_dir")" = "$required_dir" ] ||
    bootstrap_stage3_error "required Stage-2 directory is not a canonical path: $required_dir"
done

stage2_sha=$(bootstrap_stage3_hash_file "$stage2")
admitted_sha=$(bootstrap_stage3_hash_file "$admitted")
[ "$stage2_sha" = "$admitted_sha" ] || exit 1
[ "$(bootstrap_stage3_manifest_value status "$stage2_sanity")" = pass ] || exit 1
[ "$(bootstrap_stage3_manifest_value candidate_sha256_after "$stage2_sanity")" = "$admitted_sha" ] || exit 1
stage2_backend=$(bootstrap_stage3_transcript_argv_value_after \
  "$stage2_transcript" --backend) || exit 1
stage2_threads=$(bootstrap_stage3_transcript_argv_value_after \
  "$stage2_transcript" --threads) || exit 1
stage2_compile_stack_mib=$(bootstrap_stage3_transcript_argv_value_after \
  "$stage2_transcript" --compile-stack-mib 2>/dev/null || true)
stage2_progress=$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" SIMPLE_BUILD_PROGRESS_EVENTS) || exit 1
stage2_rust_log=$(bootstrap_stage3_transcript_explicit_env_value "$stage2_transcript" RUST_LOG) || exit 1
stage2_library_path=$(bootstrap_stage3_transcript_explicit_env_value "$stage2_transcript" LIBRARY_PATH) || exit 1
stage2_link_compat=$(bootstrap_stage3_transcript_explicit_env_value "$stage2_transcript" SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256) || exit 1
case "$stage2_backend" in llvm|llvm-lib|cranelift) ;; *) exit 1 ;; esac
case "$stage2_threads" in ''|*[!0-9]*|0) exit 1 ;; esac
case "$stage2_compile_stack_mib" in ''|*[!0-9]*|0) stage2_compile_stack_mib='' ;; esac
# Preserve the legacy environment order and add cache pairs only if their
# complete, unambiguous values were actually recorded by the new producer.
set -- "RUST_LOG=$stage2_rust_log" "LIBRARY_PATH=$stage2_library_path" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=$stage2_link_compat" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_NATIVE_BUILD_RUST=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$stage2_progress"
stage2_cache_replay_file="$output/stage2-cache-replay.$$.args"
bootstrap_cache_release_stage2_cache_assignments_v1 "$stage2_transcript" > "$stage2_cache_replay_file" || {
  rm -f "$stage2_cache_replay_file"
  bootstrap_stage3_error 'Stage2 cache fields incomplete, duplicated or malformed'
}
while IFS= read -r stage2_cache_assignment; do
  set -- "$@" "$stage2_cache_assignment"
done < "$stage2_cache_replay_file"
rm -f "$stage2_cache_replay_file"
set -- "$@" "SIMPLE_BINARY=$seed" native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --source src/compiler --source src/app \
  --source src/lib --entry-closure --threads "$stage2_threads"
if [ -n "$stage2_compile_stack_mib" ]; then
  set -- "$@" --compile-stack-mib "$stage2_compile_stack_mib"
fi
stage2_verbose_count=$(grep -c '^argv:9:--verbose$' "$stage2_transcript" || true)
case "$stage2_verbose_count" in 0) ;; 1) set -- "$@" --verbose ;; *) exit 1 ;; esac
set -- "$@" --cache-dir "$stage2_cache" --mode dynload --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$runtime" -o "$stage2"
stage2_args=$(bootstrap_stage3_args_sha256 "$@") || exit 1
bootstrap_stage3_verify_sanity_evidence_receipt \
  "$stage2_sanity" "$stage2" "$root"
bootstrap_stage3_verify_receiver_evidence_receipt \
  "$stage2_receiver" "$stage2" "$runtime_admitted" "$stage2_receiver_log"
bootstrap_stage3_verify_stage2_admission_receipt \
  "$stage2_admission" "$admitted" "$source_before" "$runtime_admitted" \
  "$tool_before" "$stage2_args" "$stage2_sanity" "$stage2_receiver" "$root"
path=$(bootstrap_stage3_transcript_host_value "$stage2_transcript" PATH)
cmp -s "$runtime_origin_before" "$runtime_origin_after"
cmp -s "$runtime_origin_after" "$runtime_admitted"
runtime_check="$archive/runtime-preflight.$$"
mkdir -p "$archive"
bootstrap_stage3_directory_snapshot "$runtime_check" "$runtime"
cmp -s "$runtime_admitted" "$runtime_check"
rm -f "$runtime_check"

# The Stage-2 source, Git, and tool files are immutable admission receipts.
# Compare fresh resume-time snapshots through separate temporary paths before
# acquiring the output lock or removing any prior recovery artifact; never
# overwrite the admitted records to manufacture a matching interval.
resume_source_check="$archive/source-preflight.$$"
resume_git_check="$archive/git-preflight.$$"
resume_tool_check="$archive/tool-preflight.$$"
bootstrap_stage3_source_snapshot "$resume_source_check" "$root"
bootstrap_stage3_git_state "$root" "$resume_git_check"
bootstrap_stage3_tool_authority_snapshot "$resume_tool_check" "$path" "$root"
cmp -s "$source_before" "$resume_source_check"
cmp -s "$git_before" "$resume_git_check"
cmp -s "$tool_before" "$resume_tool_check"
rm -f "$resume_source_check" "$resume_git_check" "$resume_tool_check"

if [ -f "$manifest" ] && bootstrap_stage3_verify_manifest "$manifest" "$root" "$candidate" >/dev/null 2>&1; then
  echo "error: canonical Stage 3 already converged: $manifest" >&2
  exit 1
fi
mkdir "$lock" || { echo "error: bootstrap output is locked: $lock" >&2; exit 1; }
printf '%s\n' "$$" >"$lock/pid"
bootstrap_release_resume_cleanup() {
  resume_status=$?
  bootstrap_cache_release_all
  for terminal in "$stage3_log" "$stage3_transcript" "$stage3_sanity" "$manifest"; do
    [ ! -f "$terminal" ] || cp -p "$terminal" "$archive/terminal.${terminal##*/}"
  done
  bootstrap_cache_freeze_attempt "$archive" || resume_status=1
  rm -rf -- "$lock"
  exit "$resume_status"
}
trap bootstrap_release_resume_cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

for old in "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_sanity" "$manifest"; do
  if [ -e "$old" ]; then cp -p "$old" "$archive/$(basename "$old").before-resume"; fi
done
rm -f "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_sanity" "$manifest"
bootstrap_cache_new_path_validate "$stage3_cache" || bootstrap_stage3_error 'noncanonical stage3 cache selection'
mkdir -p "$home" "$tmp" "$(dirname "$stage3_log")"

# Stage-2 authority files remain the immutable pre-build bindings. Fresh
# post-build evidence is written only to the distinct `*_after` paths below.
# Per-lane private caches: stage2 and stage3 run different compiler binaries over
# the same source tree, so each cache dir is fenced to its own lane and reuse of a
# foreign lane's dir is refused. Additive: old checkouts without the guard skip it.
# doc/05_design/compiler/incremental_build/per_lane_private_caches.md
cache_scope_guard="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)/scripts/check/check-cache-scope-ownership.shs"
if [ -f "$stage2_cache/.cache_scope" ]; then
  [ "$(cat "$stage2_cache/.cache_scope")" = lane=stage2 ] || bootstrap_stage3_error 'foreign admitted Phase 2 cache scope'
fi

# Recovery starts a fresh evidence interval after the immutable Stage-2 checks.
bootstrap_stage3_source_snapshot "$source_before" "$root"
bootstrap_stage3_git_state "$root" "$git_before"
bootstrap_stage3_tool_authority_snapshot "$tool_before" "$path" "$root"
resume_cache_action=${RESUME_STAGE3_CACHE_ACTION:-reuse}
[ "${RESUME_STAGE3_FRESH_CACHE:-0}" != 1 ] || resume_cache_action=clean
resume_cache_options=$(bootstrap_cache_release_options_v1 stripped '' absent) || exit 1
resume_cache_persistence=$(bootstrap_cache_persistence_policy) || exit 1
resume_cache_options="$resume_cache_options
$resume_cache_persistence"
resume_cache_payload=$(bootstrap_cache_phase_inputs "$root" "$platform" "$stage2_backend" \
  dynload "$source_before" "$runtime_admitted" "$tool_before" "$resume_cache_options") ||
  bootstrap_stage3_error 'cannot bind current cache inputs'
resume_cache_inputs=$(printf '%s\n' "$resume_cache_payload" | bootstrap_stage3_hash_stream) || exit 1
bootstrap_cache_prepare "$stage3" "$stage3_cache" stage3 \
  "$(bootstrap_stage3_hash_file "$admitted")" "$resume_cache_inputs" bootstrap-main \
  "$resume_cache_action" || bootstrap_stage3_error 'cache mismatch or active writer; specify explicit stage3 invalidation'
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

# See bootstrap_stage3_diagnostic_env in
# scripts/check/lib/bootstrap-stage3/authority.shs.  Computed once, word-split
# into both the args hash and the real invocation so they cannot diverge; empty
# unless an allowlisted print-only probe var is set to exactly 1.
stage3_diagnostic_env=$(bootstrap_stage3_diagnostic_env) || exit 1
stage3_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_STAGE3_STREAMING_SURFACES=1" \
  "SIMPLE_FRONTEND_CACHE=1" "SIMPLE_FRONTEND_CACHE_DIR=$stage3_cache/frontend" \
  "SIMPLE_HIR_CACHE=1" "SIMPLE_HIR_CACHE_DIR=$stage3_cache/hir" \
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
  ${stage3_diagnostic_env} \
  native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --threads 1 --cache-dir "$stage3_cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl)

bootstrap_planner_v2_verify_parent_compiler_binding \
  "$planner_admission" "$stage2" "$admitted" || exit 64

set +e
bootstrap_stage3_run_transcribed "$stage3_transcript" "$root" "$stage3_log" \
  "$home" "$tmp" "$path" RUST_LOG=error LIBRARY_PATH= \
  SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_STAGE3_STREAMING_SURFACES=1 \
  SIMPLE_FRONTEND_CACHE=1 "SIMPLE_FRONTEND_CACHE_DIR=$stage3_cache/frontend" \
  SIMPLE_HIR_CACHE=1 "SIMPLE_HIR_CACHE_DIR=$stage3_cache/hir" \
  MALLOC_ARENA_MAX=2 MALLOC_TRIM_THRESHOLD_=0 SIMPLE_NATIVE_ARENA_DECLS=1 \
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BUILD_PROGRESS_EVENTS="$progress" \
  SIMPLE_COMPILER_PHASE_PROFILE=1 \
  SIMPLE_COMPILER_PHASE_PROFILE_FILE="$phase_profile" \
  SIMPLE_MEM_SNAPSHOT_FILE="$memory_snapshot" \
  SIMPLE_EVIDENCE_RUN_ID="$evidence_run_id" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NATIVE_BUILD_TARGET="$platform" SIMPLE_NATIVE_BUILD_THREADS=1 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$stage3_cache" SIMPLE_RUNTIME_PATH="$runtime" \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap SIMPLE_BINARY="$admitted" \
  ${stage3_diagnostic_env} -- \
  "$admitted" native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --threads 1 --cache-dir "$stage3_cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl
status=$?
set -e
bootstrap_cache_report_log "$stage3_log"
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
COMPILER_PROBE_TIMEOUT_SECONDS=${COMPILER_PROBE_TIMEOUT_SECONDS:-5}
COMPILER_BUILD_TIMEOUT_SECONDS=${COMPILER_BUILD_TIMEOUT_SECONDS:-60}
COMPILER_EXEC_TIMEOUT_SECONDS=${COMPILER_EXEC_TIMEOUT_SECONDS:-5}
COMPILER_CHECK_KILL_GRACE_SECONDS=${COMPILER_CHECK_KILL_GRACE_SECONDS:-1}
. "$root/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs"
bootstrap_stage_sanity() (
  candidate_sanity=$1 evidence=$2 sanity_home=$3 sanity_tmp=$4 sanity_path=$5
  sanity_repo_root=$root
  version_expect_status=0
  version_expected=$(bootstrap_stage3_canonical_version "$sanity_repo_root") || \
    version_expect_status=1
  for name in $(env | sed 's/=.*//'); do unset "$name"; done
  HOME=$sanity_home TMPDIR=$sanity_tmp PATH=$sanity_path LC_ALL=C LANG=C
  export HOME TMPDIR PATH LC_ALL LANG
  evidence_tmp="$evidence.tmp.$$" frontend_log="$evidence_tmp.frontend"
  before=$(bootstrap_stage3_hash_file "$candidate_sanity")
  version_status=0; version=$(run_timeout 10 "$candidate_sanity" --version 2>&1) || version_status=$?
  version_match_status=1
  if [ "$version_expect_status" -eq 0 ] && \
    [ "$version" = "simple-bootstrap $version_expected" ]; then
    version_match_status=0
  fi
  unsupported_status=0
  unsupported=$(run_timeout 10 "$candidate_sanity" run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl 2>&1) || unsupported_status=$?
  frontend_status=0
  CANDIDATE_FRONTEND_BACKEND="$stage2_backend" \
    CANDIDATE_FRONTEND_BOOTSTRAP=0 \
    candidate_frontend_smoke "$candidate_sanity" >"$frontend_log" 2>&1 || frontend_status=$?
  frontend_bootstrap_status=0
  if [ "$frontend_status" -eq 0 ]; then
    CANDIDATE_FRONTEND_BACKEND="$stage2_backend" \
      CANDIDATE_FRONTEND_BOOTSTRAP=1 \
      candidate_frontend_smoke "$candidate_sanity" >>"$frontend_log" 2>&1 || \
      frontend_bootstrap_status=$?
    frontend_status=$frontend_bootstrap_status
  fi
  after=$(bootstrap_stage3_hash_file "$candidate_sanity")
  sanity_status=fail
  if [ "$version_status" -eq 0 ] && [ "$version_expect_status" -eq 0 ] && \
    [ "$version_match_status" -eq 0 ] && \
    [ "$unsupported_status" -eq 1 ] && case "$unsupported" in *"unknown command 'run'"*) true;; *) false;; esac && \
    [ "$frontend_status" -eq 0 ] && [ "$before" = "$after" ]; then sanity_status=pass; fi
  { echo schema=simple-bootstrap-sanity-evidence-v1; echo status="$sanity_status"; \
    echo candidate_sha256_before="$before"; echo version_status="$version_status"; \
    echo version_output="$version"; echo version_expected="$version_expected"; \
    echo version_expect_status="$version_expect_status"; \
    echo version_match_status="$version_match_status"; \
    echo unsupported_status="$unsupported_status"; \
    printf 'unsupported_output_sha256=%s\n' "$(printf %s "$unsupported" | bootstrap_stage3_hash_stream)"; \
    echo frontend_smoke_status="$frontend_status"; \
    echo frontend_smoke_bootstrap_mode_status="$frontend_bootstrap_status"; \
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
BSTAGE3_BACKEND=$stage2_backend BSTAGE3_MODE=dynload BSTAGE3_SEED=$seed
BSTAGE3_SEED_STAMP=$stamp BSTAGE3_NATIVE_ALL=$native_all BSTAGE3_BACKFILL=$backfill
BSTAGE3_RUNTIME_ORIGIN_BEFORE=$runtime_origin_before BSTAGE3_RUNTIME_ORIGIN_AFTER=$runtime_origin_after
BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT=$runtime_admitted BSTAGE3_TOOL_AUTHORITY=$tool_after
BSTAGE3_TOOL_AUTHORITY_BEFORE=$tool_before
BSTAGE3_STAGE2=$stage2 BSTAGE3_STAGE2_ADMITTED=$admitted
BSTAGE3_STAGE2_ADMISSION=$stage2_admission BSTAGE3_STAGE3=$candidate
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
BSTAGE3_STAGE2_SANITY=$stage2_sanity BSTAGE3_STAGE2_RECEIVER=$stage2_receiver
BSTAGE3_STAGE3_SANITY=$stage3_sanity
BSTAGE3_LOCK=$lock BSTAGE3_RUST_LOG=error
export BSTAGE3_ROOT BSTAGE3_MANIFEST BSTAGE3_PLATFORM BSTAGE3_BACKEND BSTAGE3_MODE \
  BSTAGE3_SEED BSTAGE3_SEED_STAMP BSTAGE3_NATIVE_ALL BSTAGE3_BACKFILL \
  BSTAGE3_RUNTIME_ORIGIN_BEFORE BSTAGE3_RUNTIME_ORIGIN_AFTER \
  BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT BSTAGE3_TOOL_AUTHORITY \
  BSTAGE3_TOOL_AUTHORITY_BEFORE BSTAGE3_STAGE2 BSTAGE3_STAGE2_ADMITTED \
  BSTAGE3_STAGE2_ADMISSION BSTAGE3_STAGE3 BSTAGE3_SOURCE_BEFORE BSTAGE3_SOURCE_AFTER \
  BSTAGE3_STAGE2_LOG BSTAGE3_STAGE3_LOG BSTAGE3_STAGE2_ARGS_SHA256 \
  BSTAGE3_STAGE3_ARGS_SHA256 BSTAGE3_STAGE2_THREADS BSTAGE3_STAGE3_THREADS \
  BSTAGE3_STAGE2_CACHE_DIR BSTAGE3_STAGE3_CACHE_DIR BSTAGE3_RUNTIME_PATH \
  BSTAGE3_STAGE2_COMMAND_OUTPUT BSTAGE3_STAGE3_COMMAND_OUTPUT BSTAGE3_BOOTSTRAP_SCRIPT \
  BSTAGE3_HELPER BSTAGE3_HELPER_SHA256_BEFORE BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE \
  BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE BSTAGE3_SEED_INPUTS_FINGERPRINT \
  BSTAGE3_SEED_FEATURES BSTAGE3_GIT_BEFORE BSTAGE3_GIT_AFTER \
  BSTAGE3_STAGE2_TRANSCRIPT BSTAGE3_STAGE3_TRANSCRIPT BSTAGE3_STAGE2_SANITY \
  BSTAGE3_STAGE2_RECEIVER BSTAGE3_STAGE3_SANITY BSTAGE3_LOCK BSTAGE3_RUST_LOG
bootstrap_stage3_write_manifest
bootstrap_stage3_verify_manifest "$manifest" "$root" "$candidate"
