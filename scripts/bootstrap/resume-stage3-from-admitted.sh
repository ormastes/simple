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
# Windows artifact naming.  bootstrap-from-scratch.sh already derives these
# (exe_suffix at :870/:877, archive_prefix/archive_suffix at :871/:872 and
# :902-906) and every Stage-2 artifact on disk is named accordingly:
#   simple.exe, simple.exe.inputs.sha256, simple_native_all.lib,
#   simple_compiler_backfill.lib
# This script hardcoded the POSIX names, so on Windows its very first
# fail-closed input check aborted with (measured 2026-09-03, MSVC lane):
#   ERROR - nothing was checked (required Stage-2 input missing or is a
#   symlink: .../stage2-runtime-authority/simple.inputs.sha256)
# i.e. Stage 3 resume had never been runnable on Windows at all.  The stage2
# transcript confirms the convention is a full path INCLUDING the suffix:
# `-o /d/.../build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe`.
#
# CROSS-PLATFORM IMPACT: none.  A non-Windows $platform (e.g.
# x86_64-unknown-linux-gnu) matches no case arm, so the suffix stays empty and
# the prefix/suffix stay lib/.a -- every variable below expands to the exact
# string it had before.
bootstrap_stage3_exe=''
bootstrap_stage3_arpre=lib
bootstrap_stage3_arsuf=.a
case "$platform" in
    *-windows-*) bootstrap_stage3_exe=.exe ;;
esac
case "$platform" in
    *-windows-msvc) bootstrap_stage3_arpre=''; bootstrap_stage3_arsuf=.lib ;;
esac
stage2="$output/stage2/$platform/simple$bootstrap_stage3_exe"
admitted="$stage3/stage2-admitted/simple$bootstrap_stage3_exe"
stage2_admission="$stage3/stage2-admitted/admission.env"
runtime="$stage3/stage2-runtime-authority"
seed="$runtime/simple$bootstrap_stage3_exe"
stamp="$seed.inputs.sha256"
native_all="$runtime/${bootstrap_stage3_arpre}simple_native_all${bootstrap_stage3_arsuf}"
backfill="$runtime/${bootstrap_stage3_arpre}simple_compiler_backfill${bootstrap_stage3_arsuf}"
stage2_sanity="$stage3/stage2-sanity.env"
stage2_receiver="$stage3/stage2-receiver.env"
stage2_receiver_log="$stage3/stage2-receiver.log"
stage2_transcript="$stage3/stage2-command.transcript"
stage2_log="$output/logs/$platform/stage2-native-build.log"
candidate="$stage3/simple$bootstrap_stage3_exe"
manifest="$stage3/provenance.env"
stage3_transcript="$stage3/stage3-command.transcript"
stage3_log="$output/logs/$platform/stage3-native-build.log"
stage3_status="$stage3/stage3-native-build-status.env"
stage3_sanity="$stage3/stage3-sanity.env"
stage2_cache="$stage3/stage2-native-cache"
stage3_cache="$stage3/stage3-native-cache"
# These caches are compiler-capsule caches only. Full-CLI and test-runner
# closures must use separate producer-bound paths, conventionally:
#   build/bootstrap/tool_cache/<phase>/<compiler-sha>/{full-cli,test-runner}
# Never point two compiler generations at the same writable tool cache.
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

# A self-hosted native-build controller can contain a crashed worker, print the
# worker's unsigned exit code, and still return shell status 0.  The recovery
# wrapper is the supervising parent, so it must classify both channels before
# any sanity or provenance receipt can be minted.
bootstrap_stage3_resume_effective_status() {
  bootstrap_stage3_resume_shell_status=$1
  bootstrap_stage3_resume_log=$2
  bootstrap_stage3_resume_candidate=$3
  bootstrap_stage3_resume_worker_status=absent
  bootstrap_stage3_resume_diagnostic_class=none
  bootstrap_stage3_resume_signal_identity=none
  case "$bootstrap_stage3_resume_shell_status" in
    ''|*[!0-9]*|*[0-9][0-9][0-9][0-9]*) return 125 ;;
  esac
  [ "$bootstrap_stage3_resume_shell_status" -le 255 ] || return 125
  { [ -f "$bootstrap_stage3_resume_log" ] &&
    [ ! -L "$bootstrap_stage3_resume_log" ]; } || return 125

  bootstrap_stage3_resume_worker_rows=$(grep -c \
    '^error: native-build worker exited with code ' \
    "$bootstrap_stage3_resume_log" || true)
  if [ "$bootstrap_stage3_resume_worker_rows" -ne 0 ]; then
    bootstrap_stage3_resume_worker_status=$(sed -n \
      's/^error: native-build worker exited with code \([0-9][0-9]*\)[.]$/\1/p' \
      "$bootstrap_stage3_resume_log" | tail -n 1)
    [ -n "$bootstrap_stage3_resume_worker_status" ] || \
      bootstrap_stage3_resume_worker_status=malformed
    bootstrap_stage3_resume_diagnostic_class=worker-nonzero-exit
    if [ "$bootstrap_stage3_resume_worker_status" = 4294967295 ]; then
      # Simple's process facade represents its signed -1 sentinel as u32 in
      # this compiled lane. It means signal OR wait failure, not a known
      # signal number; retain that distinction instead of inventing SIGSEGV.
      bootstrap_stage3_resume_diagnostic_class=worker-signal-or-wait-failure
      bootstrap_stage3_resume_signal_identity=unresolved-signal-or-wait-failure
    fi
  fi
  if grep -q '^timeout: .* dumped core$' "$bootstrap_stage3_resume_log"; then
    bootstrap_stage3_resume_diagnostic_class=worker-core-dump
    bootstrap_stage3_resume_signal_identity=core-dump-signal-unspecified
    return 1
  fi
  if [ "$bootstrap_stage3_resume_worker_rows" -ne 0 ]; then
    return 1
  fi
  if [ "$bootstrap_stage3_resume_shell_status" -ge 128 ]; then
    bootstrap_stage3_resume_diagnostic_class=shell-signal-exit
    bootstrap_stage3_resume_signal_identity=signal-number-$((bootstrap_stage3_resume_shell_status - 128))
  elif [ "$bootstrap_stage3_resume_shell_status" -ne 0 ]; then
    bootstrap_stage3_resume_diagnostic_class=shell-nonzero-exit
  fi
  [ "$bootstrap_stage3_resume_shell_status" -eq 0 ] || \
    return "$bootstrap_stage3_resume_shell_status"
  { [ -f "$bootstrap_stage3_resume_candidate" ] &&
    [ ! -L "$bootstrap_stage3_resume_candidate" ] &&
    [ -x "$bootstrap_stage3_resume_candidate" ]; } || {
      bootstrap_stage3_resume_diagnostic_class=missing-executable-candidate
      return 1
    }
  return 0
}

bootstrap_stage3_resume_write_status_receipt() {
  bootstrap_stage3_resume_receipt=$1
  bootstrap_stage3_resume_receipt_log=$2
  bootstrap_stage3_resume_receipt_transcript=$3
  bootstrap_stage3_resume_receipt_shell_status=$4
  bootstrap_stage3_resume_receipt_effective_status=$5
  bootstrap_stage3_resume_receipt_worker_status=$6
  bootstrap_stage3_resume_receipt_requested_route=$7
  bootstrap_stage3_resume_receipt_fallback_route=$8
  bootstrap_stage3_resume_receipt_diagnostic_class=$9
  shift 9
  bootstrap_stage3_resume_receipt_signal_identity=$1
  bootstrap_stage3_resume_receipt_tmp="${bootstrap_stage3_resume_receipt}.tmp.$$"
  [ ! -L "$bootstrap_stage3_resume_receipt" ] || return 125
  [ ! -e "$bootstrap_stage3_resume_receipt_tmp" ] &&
    [ ! -L "$bootstrap_stage3_resume_receipt_tmp" ] || return 125
  bootstrap_stage3_resume_receipt_result=fail
  [ "$bootstrap_stage3_resume_receipt_effective_status" -ne 0 ] ||
    bootstrap_stage3_resume_receipt_result=pass
  {
    echo schema=simple-bootstrap-stage3-native-build-status-v1
    echo status="$bootstrap_stage3_resume_receipt_result"
    echo shell_exit_status="$bootstrap_stage3_resume_receipt_shell_status"
    echo effective_exit_status="$bootstrap_stage3_resume_receipt_effective_status"
    echo worker_exit_status="$bootstrap_stage3_resume_receipt_worker_status"
    echo requested_route="$bootstrap_stage3_resume_receipt_requested_route"
    echo fallback_route="$bootstrap_stage3_resume_receipt_fallback_route"
    echo diagnostic_class="$bootstrap_stage3_resume_receipt_diagnostic_class"
    echo signal_identity="$bootstrap_stage3_resume_receipt_signal_identity"
    echo log_sha256="$(bootstrap_stage3_hash_file \
      "$bootstrap_stage3_resume_receipt_log")"
    echo transcript_sha256="$(bootstrap_stage3_hash_file \
      "$bootstrap_stage3_resume_receipt_transcript")"
  } >"$bootstrap_stage3_resume_receipt_tmp" || {
    rm -f "$bootstrap_stage3_resume_receipt_tmp"
    return 125
  }
  mv "$bootstrap_stage3_resume_receipt_tmp" \
    "$bootstrap_stage3_resume_receipt" || {
    rm -f "$bootstrap_stage3_resume_receipt_tmp"
    return 125
  }
}

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
case "$stage2_backend" in llvm|llvm-lib|cranelift) ;; *) exit 1 ;; esac
case "$stage2_threads" in ''|*[!0-9]*|0) exit 1 ;; esac
case "$stage2_compile_stack_mib" in ''|*[!0-9]*|0) stage2_compile_stack_mib='' ;; esac
if [ -n "$stage2_compile_stack_mib" ]; then
  stage2_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_NATIVE_BUILD_RUST=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$stage2_progress" "SIMPLE_BINARY=$seed" \
  native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --source src/compiler --source src/app \
  --source src/lib --entry-closure --threads "$stage2_threads" \
  --compile-stack-mib "$stage2_compile_stack_mib" \
  --cache-dir "$stage2_cache" --mode dynload --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$runtime" -o "$stage2")
else
  stage2_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_NATIVE_BUILD_RUST=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$stage2_progress" "SIMPLE_BINARY=$seed" \
  native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --source src/compiler --source src/app \
  --source src/lib --entry-closure --threads "$stage2_threads" \
  --cache-dir "$stage2_cache" --mode dynload --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$runtime" -o "$stage2")
fi
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
# Each cmp IS the refusal: a bare 'cmp -s' under 'set -eu' aborts the script
# when the snapshots differ.  That enforcement is correct and is unchanged
# below -- what was missing is the reason.  Measured 2026-09-03: a resume whose
# only drift was a moved git HEAD ran its full ~13-minute preflight and exited 1
# having printed NOTHING, which is exactly the silent-exit failure this file's
# own header names as having made a real Stage-2 refusal undiagnosable.  Saying
# which of source/git/tool differs turns a blind 13-minute run into a one-line
# answer.  Same exit status and same abort point as before; only stderr gains a
# line.  CROSS-PLATFORM IMPACT: none, nothing here is OS-dependent.
cmp -s "$source_before" "$resume_source_check" || {
  echo "error: Stage-2 source snapshot changed since admission: $source_before differs from $resume_source_check" >&2
  exit 1
}
cmp -s "$git_before" "$resume_git_check" || {
  echo "error: Stage-2 git state changed since admission: $git_before differs from $resume_git_check (re-mint Stage 2 over the current tree)" >&2
  exit 1
}
cmp -s "$tool_before" "$resume_tool_check" || {
  echo "error: Stage-2 tool authority changed since admission: $tool_before differs from $resume_tool_check" >&2
  exit 1
}
rm -f "$resume_source_check" "$resume_git_check" "$resume_tool_check"

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

for old in "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_status" "$stage3_sanity" "$manifest"; do
  if [ -e "$old" ]; then cp -p "$old" "$archive/$(basename "$old").before-resume"; fi
done
rm -f "$candidate" "$stage3_transcript" "$stage3_log" "$stage3_status" "$stage3_sanity" "$manifest"
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

# Stage-2 authority files remain the immutable pre-build bindings. Fresh
# post-build evidence is written only to the distinct `*_after` paths below.
# Per-lane private caches: stage2 and stage3 run different compiler binaries over
# the same source tree, so each cache dir is fenced to its own lane and reuse of a
# foreign lane's dir is refused. Additive: old checkouts without the guard skip it.
# doc/05_design/compiler/incremental_build/per_lane_private_caches.md
cache_scope_guard="$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)/scripts/check/check-cache-scope-ownership.shs"
if [ -f "$cache_scope_guard" ]; then
  mkdir -p "$stage2_cache"
  sh "$cache_scope_guard" "$stage2_cache" stage2 || exit 1
  sh "$cache_scope_guard" "$stage3_cache" stage3 || exit 1
fi

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

# See bootstrap_stage3_diagnostic_env in
# scripts/check/lib/bootstrap-stage3/authority.shs.  Computed once, word-split
# into both the args hash and the real invocation so they cannot diverge; empty
# unless an allowlisted print-only probe var is set to exactly 1.
stage3_diagnostic_env=$(bootstrap_stage3_diagnostic_env) || exit 1
# Opt-in parallelism / per-file timeout for the Stage 3 recompile.  Unset
# reproduces the pinned `--threads 1` argv byte-for-byte.  Baked into both the
# args hash and the transcribed invocation (the child runs under `env -i`, so
# an outer variable would never reach it).  `full` = online CPUs.
stage3_threads=${SIMPLE_NATIVE_BUILD_THREADS:-1}
[ "$stage3_threads" != full ] ||
  stage3_threads=$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || echo 1)
case "$stage3_threads" in ''|*[!0-9]*|0) exit 1 ;; esac
stage3_requested_route=direct
stage3_fallback_route=none
if [ "$stage3_threads" -gt 1 ]; then
  stage3_requested_route=coordinator
  stage3_fallback_route=direct
fi
stage3_timeout_args=
case "${SIMPLE_NATIVE_FILE_TIMEOUT:-}" in
  '') ;;
  *[!0-9]*) exit 1 ;;
  *) stage3_timeout_args="--timeout $SIMPLE_NATIVE_FILE_TIMEOUT" ;;
esac
# Allocatable mission-critical mode for the Stage 3 recompile (step 1,
# 2026-08-28).  OPT-IN: `SIMPLE_STAGE3_MISSION_CRITICAL=1` pins the assurance
# profile to `critical` (driver_types.spl reads SIMPLE_SAFETY_PROFILE into
# CompileContext.assurance_policy; the safety pass DENIES at critical) and
# turns the WARNING PHASE on (driver_safety_severity.safety_pass_severity_phased
# drops that Deny to Warn), so the recompile stays green while every violation
# is printed.  Unset reproduces the pinned argv byte-for-byte.  Baked into both
# the args hash and the transcribed invocation, exactly like the threads knob
# above, because the child runs under `env -i`.  Flipping this to default-on is
# the "mission-critical default for phase 3" lane and is deliberately NOT done
# here: it changes the Stage 3 args hash for every existing admission receipt.
stage3_mc_env=
case "${SIMPLE_STAGE3_MISSION_CRITICAL:-}" in
  '') ;;
  1) stage3_mc_env="SIMPLE_SAFETY_PROFILE=critical SIMPLE_ASSURANCE_WARNING_PHASE=1" ;;
  *) echo "error: SIMPLE_STAGE3_MISSION_CRITICAL must be unset or exactly 1" >&2; exit 1 ;;
esac
stage3_args=$(bootstrap_stage3_args_sha256 \
  "RUST_LOG=error" "LIBRARY_PATH=" "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent" \
  "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
  "SIMPLE_STAGE3_STREAMING_SURFACES=1" \
  "SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE=$stage3_requested_route" \
  "SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE=$stage3_fallback_route" \
  "SIMPLE_FRONTEND_CACHE=0" \
  "MALLOC_ARENA_MAX=2" "MALLOC_TRIM_THRESHOLD_=0" \
  "SIMPLE_NATIVE_ARENA_DECLS=1" "SIMPLE_NO_STUB_FALLBACK=1" \
  ${stage3_mc_env} \
  "SIMPLE_BUILD_PROGRESS_EVENTS=$progress" \
  "SIMPLE_COMPILER_PHASE_PROFILE=1" \
  "SIMPLE_COMPILER_PHASE_PROFILE_FILE=$phase_profile" \
  "SIMPLE_MEM_SNAPSHOT_FILE=$memory_snapshot" \
  "SIMPLE_EVIDENCE_RUN_ID=$evidence_run_id" \
  "LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1" \
  "SIMPLE_NATIVE_BUILD_TARGET=$platform" "SIMPLE_NATIVE_BUILD_THREADS=$stage3_threads" \
  "SIMPLE_NATIVE_BUILD_CACHE_DIR=$stage3_cache" "SIMPLE_RUNTIME_PATH=$runtime" \
  "SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap" "SIMPLE_BINARY=$admitted" \
  ${stage3_diagnostic_env} \
  native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --threads "$stage3_threads" \
  ${stage3_timeout_args} --cache-dir "$stage3_cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl)

bootstrap_planner_v2_verify_parent_compiler_binding \
  "$planner_admission" "$stage2" "$admitted" || exit 64

set +e
bootstrap_stage3_run_transcribed "$stage3_transcript" "$root" "$stage3_log" \
  "$home" "$tmp" "$path" RUST_LOG=error LIBRARY_PATH= \
  SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent SIMPLE_BOOTSTRAP=1 \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_STAGE3_STREAMING_SURFACES=1 \
  SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE="$stage3_requested_route" \
  SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE="$stage3_fallback_route" \
  SIMPLE_FRONTEND_CACHE=0 \
  MALLOC_ARENA_MAX=2 MALLOC_TRIM_THRESHOLD_=0 SIMPLE_NATIVE_ARENA_DECLS=1 \
  SIMPLE_NO_STUB_FALLBACK=1 ${stage3_mc_env} \
  SIMPLE_BUILD_PROGRESS_EVENTS="$progress" \
  SIMPLE_COMPILER_PHASE_PROFILE=1 \
  SIMPLE_COMPILER_PHASE_PROFILE_FILE="$phase_profile" \
  SIMPLE_MEM_SNAPSHOT_FILE="$memory_snapshot" \
  SIMPLE_EVIDENCE_RUN_ID="$evidence_run_id" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NATIVE_BUILD_TARGET="$platform" SIMPLE_NATIVE_BUILD_THREADS="$stage3_threads" \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$stage3_cache" SIMPLE_RUNTIME_PATH="$runtime" \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap SIMPLE_BINARY="$admitted" \
  ${stage3_diagnostic_env} -- \
  "$admitted" native-build --target "$platform" --backend "$stage2_backend" \
  --runtime-bundle core-c-bootstrap --threads "$stage3_threads" \
  ${stage3_timeout_args} --cache-dir "$stage3_cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl
status=$?
set -e
effective_status=0
bootstrap_stage3_resume_effective_status "$status" "$stage3_log" \
  "$candidate" || effective_status=$?
worker_status=$bootstrap_stage3_resume_worker_status
diagnostic_class=$bootstrap_stage3_resume_diagnostic_class
signal_identity=$bootstrap_stage3_resume_signal_identity
if ! bootstrap_stage3_resume_write_status_receipt "$stage3_status" \
  "$stage3_log" "$stage3_transcript" "$status" "$effective_status" \
  "$worker_status" "$stage3_requested_route" "$stage3_fallback_route" \
  "$diagnostic_class" "$signal_identity"; then
  rm -f "$candidate" "$stage3_sanity" "$manifest"
  echo "error: Stage 3 native-build status receipt publication failed" >&2
  exit 125
fi
if [ "$effective_status" -ne 0 ]; then
  rm -f "$candidate" "$stage3_sanity" "$manifest"
  echo "error: Stage 3 native-build failed (shell=$status worker=$worker_status effective=$effective_status class=$diagnostic_class signal=$signal_identity route=$stage3_requested_route fallback=$stage3_fallback_route)" >&2
  exit "$effective_status"
fi
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
BSTAGE3_STAGE2_THREADS=$stage2_threads BSTAGE3_STAGE3_THREADS=$stage3_threads
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
