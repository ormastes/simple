#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)
source_output=${1:?usage: resume-stage3-from-admitted.sh OUTPUT_DIR}
case "$source_output" in /*|*../*|../*|*/..|..) exit 2 ;; esac
output="$root/$source_output"
[ -d "$output" ] && [ ! -L "$output" ] || exit 1
[ "$(CDPATH= cd -- "$output" && pwd -P)" = "$output" ] || exit 1

BOOTSTRAP_STAGE3_FACADE_PATH="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
export BOOTSTRAP_STAGE3_FACADE_PATH
. "$BOOTSTRAP_STAGE3_FACADE_PATH"

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
original_source_before="$stage3/source-inputs-before.txt"
original_git_before="$stage3/git-state-before.env"
original_tool_before="$stage3/tool-authority-before.txt"
runtime_origin_before="$stage3/runtime-origin-before.txt"
runtime_origin_after="$stage3/runtime-origin-after.txt"
runtime_admitted="$stage3/runtime-admitted.txt"
runtime_before_stage2="$stage3/runtime-before-stage2.txt"
runtime_after_stage2="$stage3/runtime-after-stage2.txt"
candidate="$stage3/simple"
manifest="$stage3/provenance.env"
stage3_transcript="$stage3/stage3-command.transcript"
stage3_log="$output/logs/$platform/stage3-native-build.log"
stage3_sanity="$stage3/stage3-sanity.env"
stage2_cache="$stage3/stage2-native-cache"
stage3_cache="$stage3/stage3-native-cache"
home="$stage3/stage3-resume-home"
tmp="$stage3/stage3-resume-tmp"
resume_source_before="$stage3/resume-source-inputs-before.txt"
resume_source_after="$stage3/resume-source-inputs-after.txt"
resume_git_before="$stage3/resume-git-state-before.env"
resume_git_after="$stage3/resume-git-state-after.env"
resume_tool_before="$stage3/resume-tool-authority-before.txt"
resume_tool_after="$stage3/resume-tool-authority-after.txt"
resume_runtime_before="$stage3/resume-runtime-before-stage3.txt"
resume_runtime_after="$stage3/resume-runtime-after-stage3.txt"
lock="$output.lock"
archive="$stage3/stage3-resume-archive"

for required in "$stage2" "$admitted" "$seed" "$stamp" "$native_all" \
  "$stage2_sanity" "$stage2_transcript" "$stage2_log" \
  "$original_source_before" "$original_git_before" "$original_tool_before" \
  "$runtime_origin_before" "$runtime_origin_after" "$runtime_admitted" \
  "$runtime_before_stage2" "$runtime_after_stage2"; do
  [ -f "$required" ] && [ ! -L "$required" ] || exit 1
  [ "$(bootstrap_stage3_canonical_file "$required")" = "$required" ] || exit 1
done
for required_dir in "$stage3" "$runtime" "$stage2_cache"; do
  [ -d "$required_dir" ] && [ ! -L "$required_dir" ] || exit 1
  [ "$(bootstrap_stage3_canonical_path "$required_dir")" = "$required_dir" ] || exit 1
done

# Refuse ambiguous recovery state before creating the lock or any receipt.
[ ! -e "$manifest" ] && [ ! -L "$manifest" ] || {
  echo "error: Stage 3 provenance already exists; refusing recovery" >&2
  exit 1
}
[ ! -L "$archive" ] || {
  echo "error: Stage 3 recovery archive is a symlink" >&2
  exit 1
}
if [ -e "$archive" ]; then
  [ -d "$archive" ] &&
    [ "$(bootstrap_stage3_canonical_path "$archive")" = "$archive" ] || exit 1
fi
[ ! -e "$lock" ] && [ ! -L "$lock" ] || {
  echo "error: bootstrap output is locked" >&2
  exit 1
}
for mutable in "$candidate" "$stage3_transcript" "$stage3_log" \
  "$stage3_sanity" "$stage3_cache" "$home" "$tmp" \
  "$resume_source_before" "$resume_source_after" \
  "$resume_git_before" "$resume_git_after" \
  "$resume_tool_before" "$resume_tool_after" \
  "$resume_runtime_before" "$resume_runtime_after"; do
  [ ! -L "$mutable" ] || {
    echo "error: symlinked Stage 3 recovery state: $mutable" >&2
    exit 1
  }
done

stage2_sha=$(bootstrap_stage3_hash_file "$stage2")
admitted_sha=$(bootstrap_stage3_hash_file "$admitted")
[ "$stage2_sha" = "$admitted_sha" ] || exit 1
[ "$(bootstrap_stage3_manifest_value status "$stage2_sanity")" = pass ] || exit 1
[ "$(bootstrap_stage3_manifest_value candidate_sha256_before "$stage2_sanity")" = "$admitted_sha" ] || exit 1
[ "$(bootstrap_stage3_manifest_value candidate_sha256_after "$stage2_sanity")" = "$admitted_sha" ] || exit 1
cmp -s "$runtime_origin_before" "$runtime_origin_after"
cmp -s "$runtime_origin_after" "$runtime_admitted"
cmp -s "$runtime_admitted" "$runtime_before_stage2"
cmp -s "$runtime_admitted" "$runtime_after_stage2"
original_source_sha=$(bootstrap_stage3_hash_file "$original_source_before")
original_git_sha=$(bootstrap_stage3_hash_file "$original_git_before")
original_tool_sha=$(bootstrap_stage3_hash_file "$original_tool_before")
runtime_origin_before_sha=$(bootstrap_stage3_hash_file "$runtime_origin_before")
runtime_origin_after_sha=$(bootstrap_stage3_hash_file "$runtime_origin_after")
runtime_admitted_sha=$(bootstrap_stage3_hash_file "$runtime_admitted")
runtime_before_stage2_sha=$(bootstrap_stage3_hash_file "$runtime_before_stage2")
runtime_after_stage2_sha=$(bootstrap_stage3_hash_file "$runtime_after_stage2")

mkdir "$lock" || exit 1
[ -d "$lock" ] && [ ! -L "$lock" ] &&
  [ "$(bootstrap_stage3_canonical_path "$lock")" = "$lock" ] || exit 1
printf '%s\n' "$$" >"$lock/pid"
release_lock() {
  if [ -d "$lock" ] && [ ! -L "$lock" ] && [ -f "$lock/pid" ] &&
    [ ! -L "$lock/pid" ] && [ "$(tr -d '[:space:]' <"$lock/pid")" = "$$" ]; then
    rm -rf "$lock"
  fi
}
trap release_lock EXIT HUP INT TERM

bootstrap_stage3_directory_snapshot "$lock/runtime-preflight.txt" "$runtime"
cmp -s "$runtime_admitted" "$lock/runtime-preflight.txt"
rm -f "$lock/runtime-preflight.txt"

mkdir -p "$archive"
[ -d "$archive" ] && [ ! -L "$archive" ] &&
  [ "$(bootstrap_stage3_canonical_path "$archive")" = "$archive" ] || exit 1
run_archive=$(mktemp -d "$archive/run.XXXXXX")
[ -d "$run_archive" ] && [ ! -L "$run_archive" ] &&
  [ "$(bootstrap_stage3_canonical_path "$run_archive")" = "$run_archive" ] || exit 1
for old in "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_sanity" \
  "$stage3_cache" "$home" "$tmp" "$resume_source_before" \
  "$resume_source_after" "$resume_git_before" "$resume_git_after" \
  "$resume_tool_before" "$resume_tool_after" \
  "$resume_runtime_before" "$resume_runtime_after"; do
  if [ -e "$old" ]; then
    mv "$old" "$run_archive/$(basename "$old").before-resume"
  fi
done

# Replay immutable Stage 2 evidence only after owning the output lock.
stage2_home=$(bootstrap_stage3_transcript_host_value "$stage2_transcript" HOME)
stage2_tmp=$(bootstrap_stage3_transcript_host_value "$stage2_transcript" TMPDIR)
path=$(bootstrap_stage3_transcript_host_value "$stage2_transcript" PATH)
rust_log=$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" RUST_LOG)
library_path=$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" LIBRARY_PATH)
link_compat=$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256)
[ "$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" SIMPLE_BOOTSTRAP)" = 1 ]
[ "$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" SIMPLE_NO_DEPRECATED_WARNINGS)" = 1 ]
[ "$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" SIMPLE_NATIVE_BUILD_RUST)" = 1 ]
[ "$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" SIMPLE_NO_STUB_FALLBACK)" = 1 ]
[ "$(bootstrap_stage3_transcript_explicit_env_value \
  "$stage2_transcript" SIMPLE_BINARY)" = "$seed" ]

stage2_threads=$(awk '
  $0 == "argv:9:--threads" { if (seen++) exit 2; getline; sub(/^argv:[0-9]+:/, ""); value=$0 }
  END { if (seen != 1 || value == "") exit 1; print value }
' "$stage2_transcript")
case "$stage2_threads" in ''|*[!0-9]*) exit 1 ;; esac
verbose_count=$(grep -Fxc 'argv:9:--verbose' "$stage2_transcript" || true)
case "$verbose_count" in 0) stage2_verbose= ;; 1) stage2_verbose=--verbose ;; *) exit 1 ;; esac

bootstrap_stage3_verify_command_transcript "$stage2_transcript" "$root" \
  "RUST_LOG=$rust_log" "LIBRARY_PATH=$library_path" \
  "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=$link_compat" \
  SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1 \
  "SIMPLE_BINARY=$seed" -- "$seed" native-build --target "$platform" \
  --backend cranelift --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib --entry-closure \
  --threads "$stage2_threads" ${stage2_verbose:+$stage2_verbose} \
  --cache-dir "$stage2_cache" --mode dynload \
  --entry src/app/cli/bootstrap_main.spl --runtime-path "$runtime" -o "$stage2"
bootstrap_stage3_verify_sanity_evidence "$stage2_sanity" "$stage2" "$root" \
  cranelift "$stage2_home" "$stage2_tmp" "$path"
[ "$(bootstrap_stage3_hash_file "$stage2")" = "$stage2_sha" ]
[ "$(bootstrap_stage3_hash_file "$admitted")" = "$admitted_sha" ]

# Establish a distinct Stage 3 recovery interval without altering Stage 2 receipts.
bootstrap_stage3_source_snapshot "$resume_source_before" "$root"
cmp -s "$original_source_before" "$resume_source_before"
bootstrap_stage3_git_state "$root" "$resume_git_before"
cmp -s "$original_git_before" "$resume_git_before"
bootstrap_stage3_tool_authority_snapshot "$resume_tool_before" "$path" "$root"
cmp -s "$original_tool_before" "$resume_tool_before"
bootstrap_stage3_directory_snapshot "$resume_runtime_before" "$runtime"
cmp -s "$runtime_admitted" "$resume_runtime_before"

mkdir -p "$stage3_cache" "$home" "$tmp" "$(dirname "$stage3_log")"
for fresh_dir in "$stage3_cache" "$home" "$tmp"; do
  [ -d "$fresh_dir" ] && [ ! -L "$fresh_dir" ] &&
    [ "$(bootstrap_stage3_canonical_path "$fresh_dir")" = "$fresh_dir" ] || exit 1
done

script="$root/scripts/bootstrap/bootstrap-from-scratch.sh"
helper="$BOOTSTRAP_STAGE3_FACADE_PATH"
script_sha_before=$(bootstrap_stage3_hash_file "$script")
helper_sha_before=$(bootstrap_stage3_hash_file "$helper")
helper_bundle_before=$(bootstrap_stage3_helper_bundle_fingerprint)
seed_fingerprint=$(bootstrap_stage3_manifest_value inputs_fingerprint "$stamp")

stage2_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=$rust_log" "LIBRARY_PATH=$library_path" \
  "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=$link_compat" \
  SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1 \
  "SIMPLE_BINARY=$seed" native-build --target "$platform" \
  --backend cranelift --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib --entry-closure \
  --threads "$stage2_threads" ${stage2_verbose:+$stage2_verbose} \
  --cache-dir "$stage2_cache" --mode dynload \
  --entry src/app/cli/bootstrap_main.spl --runtime-path "$runtime" -o "$stage2")
stage3_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=$rust_log" "LIBRARY_PATH=$library_path" \
  "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=$link_compat" \
  SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_NATIVE_ARENA_DECLS=1 SIMPLE_NO_STUB_FALLBACK=1 \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  "SIMPLE_NATIVE_BUILD_TARGET=$platform" SIMPLE_NATIVE_BUILD_THREADS=1 \
  "SIMPLE_NATIVE_BUILD_CACHE_DIR=$stage3_cache" \
  "SIMPLE_RUNTIME_PATH=$runtime" SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
  "SIMPLE_BINARY=$admitted" native-build --target "$platform" \
  --backend cranelift --runtime-bundle core-c-bootstrap --entry-closure \
  --threads 1 --cache-dir "$stage3_cache" --mode dynload \
  --runtime-path "$runtime" --entry src/app/cli/bootstrap_main.spl -o "$candidate")

set +e
bootstrap_stage3_run_transcribed "$stage3_transcript" "$root" "$stage3_log" \
  "$home" "$tmp" "$path" "RUST_LOG=$rust_log" \
  "LIBRARY_PATH=$library_path" \
  "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=$link_compat" \
  SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_NATIVE_ARENA_DECLS=1 SIMPLE_NO_STUB_FALLBACK=1 \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  "SIMPLE_NATIVE_BUILD_TARGET=$platform" SIMPLE_NATIVE_BUILD_THREADS=1 \
  "SIMPLE_NATIVE_BUILD_CACHE_DIR=$stage3_cache" \
  "SIMPLE_RUNTIME_PATH=$runtime" SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
  "SIMPLE_BINARY=$admitted" -- "$admitted" native-build \
  --target "$platform" --backend cranelift --runtime-bundle core-c-bootstrap \
  --entry-closure --threads 1 --cache-dir "$stage3_cache" --mode dynload \
  --runtime-path "$runtime" --entry src/app/cli/bootstrap_main.spl -o "$candidate"
status=$?
set -e
[ "$status" -eq 0 ] || exit "$status"
[ -x "$candidate" ] && [ ! -L "$candidate" ] || exit 1
[ "$(bootstrap_stage3_hash_file "$admitted")" = "$admitted_sha" ] || exit 1
bootstrap_stage3_directory_snapshot "$resume_runtime_after" "$runtime"
cmp -s "$resume_runtime_before" "$resume_runtime_after"

CANDIDATE_FRONTEND_ROOT=$root
COMPILER_PROBE_TIMEOUT_SECONDS=5
COMPILER_BUILD_TIMEOUT_SECONDS=60
COMPILER_EXEC_TIMEOUT_SECONDS=5
COMPILER_CHECK_KILL_GRACE_SECONDS=1
. "$root/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs"
bootstrap_stage_sanity() (
  sanity_candidate=$1 evidence=$2 sanity_home=$3 sanity_tmp=$4 sanity_path=$5
  for name in $(env | sed 's/=.*//'); do unset "$name"; done
  HOME=$sanity_home TMPDIR=$sanity_tmp PATH=$sanity_path LC_ALL=C LANG=C
  export HOME TMPDIR PATH LC_ALL LANG
  evidence_tmp="$evidence.tmp.$$" frontend_log="$evidence_tmp.frontend"
  before=$(bootstrap_stage3_hash_file "$sanity_candidate")
  version_status=0
  version=$(run_timeout 10 "$sanity_candidate" --version 2>&1) || version_status=$?
  unsupported_status=0
  unsupported=$(run_timeout 10 "$sanity_candidate" run \
    scripts/check/cert/redeploy_gate/fixtures/p2_add.spl 2>&1) || unsupported_status=$?
  frontend_status=0
  CANDIDATE_FRONTEND_BACKEND=cranelift \
    candidate_frontend_smoke "$sanity_candidate" >"$frontend_log" 2>&1 || frontend_status=$?
  after=$(bootstrap_stage3_hash_file "$sanity_candidate")
  sanity_status=fail
  if [ "$version_status" -eq 0 ] && [ "$version" = "simple-bootstrap 1.0.0-beta" ] &&
    [ "$unsupported_status" -eq 1 ] &&
    case "$unsupported" in *"unknown command 'run'"*) true ;; *) false ;; esac &&
    [ "$frontend_status" -eq 0 ] && [ "$before" = "$after" ]; then
    sanity_status=pass
  fi
  {
    echo schema=simple-bootstrap-sanity-evidence-v1
    echo status="$sanity_status"
    echo candidate_sha256_before="$before"
    echo version_status="$version_status"
    echo version_output="$version"
    echo unsupported_status="$unsupported_status"
    printf 'unsupported_output_sha256=%s\n' \
      "$(printf %s "$unsupported" | bootstrap_stage3_hash_stream)"
    echo frontend_smoke_status="$frontend_status"
    echo frontend_smoke_output_sha256="$(bootstrap_stage3_hash_file "$frontend_log")"
    echo candidate_sha256_after="$after"
  } >"$evidence_tmp"
  mv "$evidence_tmp" "$evidence"
  rm -f "$frontend_log"
  [ "$sanity_status" = pass ]
)
bootstrap_stage_sanity "$candidate" "$stage3_sanity" "$home" "$tmp" "$path"
bootstrap_stage3_source_snapshot "$resume_source_after" "$root"
bootstrap_stage3_git_state "$root" "$resume_git_after"
bootstrap_stage3_tool_authority_snapshot "$resume_tool_after" "$path" "$root"
cmp -s "$resume_source_before" "$resume_source_after"
cmp -s "$resume_git_before" "$resume_git_after"
cmp -s "$resume_tool_before" "$resume_tool_after"
[ "$(bootstrap_stage3_hash_file "$original_source_before")" = "$original_source_sha" ]
[ "$(bootstrap_stage3_hash_file "$original_git_before")" = "$original_git_sha" ]
[ "$(bootstrap_stage3_hash_file "$original_tool_before")" = "$original_tool_sha" ]
[ "$(bootstrap_stage3_hash_file "$runtime_origin_before")" = "$runtime_origin_before_sha" ]
[ "$(bootstrap_stage3_hash_file "$runtime_origin_after")" = "$runtime_origin_after_sha" ]
[ "$(bootstrap_stage3_hash_file "$runtime_admitted")" = "$runtime_admitted_sha" ]
[ "$(bootstrap_stage3_hash_file "$runtime_before_stage2")" = "$runtime_before_stage2_sha" ]
[ "$(bootstrap_stage3_hash_file "$runtime_after_stage2")" = "$runtime_after_stage2_sha" ]

BSTAGE3_ROOT=$root BSTAGE3_MANIFEST=$manifest BSTAGE3_PLATFORM=$platform
BSTAGE3_BACKEND=cranelift BSTAGE3_MODE=dynload BSTAGE3_SEED=$seed
BSTAGE3_SEED_STAMP=$stamp BSTAGE3_NATIVE_ALL=$native_all BSTAGE3_BACKFILL=$backfill
BSTAGE3_RUNTIME_ORIGIN_BEFORE=$runtime_origin_before BSTAGE3_RUNTIME_ORIGIN_AFTER=$runtime_origin_after
BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT=$runtime_admitted BSTAGE3_TOOL_AUTHORITY=$resume_tool_after
BSTAGE3_STAGE2=$stage2 BSTAGE3_STAGE2_ADMITTED=$admitted BSTAGE3_STAGE3=$candidate
BSTAGE3_SOURCE_BEFORE=$resume_source_before BSTAGE3_SOURCE_AFTER=$resume_source_after
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
BSTAGE3_GIT_BEFORE=$resume_git_before BSTAGE3_GIT_AFTER=$resume_git_after
BSTAGE3_STAGE2_TRANSCRIPT=$stage2_transcript BSTAGE3_STAGE3_TRANSCRIPT=$stage3_transcript
BSTAGE3_STAGE2_SANITY=$stage2_sanity BSTAGE3_STAGE3_SANITY=$stage3_sanity
BSTAGE3_LOCK=$lock BSTAGE3_RUST_LOG=$rust_log
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
