#!/bin/sh

# Keep bootstrap and every non-detached descendant in one dedicated kernel
# process group. Lock recovery remains fail-closed while any group member lives.
bootstrap_entry_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P) || exit 70
bootstrap_session_helper=\
"${bootstrap_entry_dir}/../check/lib/portable-session-exec.pl"
if [ "${SIMPLE_BOOTSTRAP_SESSION_READY:-0}" = 1 ]; then
  bootstrap_session_identity=$(perl "${bootstrap_session_helper}" \
    --identity-parent) || {
    echo "error: bootstrap could not verify its native session identity" >&2
    exit 70
  }
  bootstrap_session_pid=$(printf '%s\n' "${bootstrap_session_identity}" |
    sed -n 's/^pid=//p')
  bootstrap_session_pgid=$(printf '%s\n' "${bootstrap_session_identity}" |
    sed -n 's/^pgid=//p')
  case "${bootstrap_session_pid}" in
    ''|*[!0-9]*) bootstrap_session_pid=invalid ;;
  esac
  case "${bootstrap_session_pgid}" in
    ''|*[!0-9]*) bootstrap_session_pgid=invalid ;;
  esac
  [ "${bootstrap_session_pid}" = "${bootstrap_session_pgid}" ] || {
    echo "error: bootstrap session guard was bypassed without PID=PGID" >&2
    exit 70
  }
else
  SIMPLE_BOOTSTRAP_SESSION_READY=1
  export SIMPLE_BOOTSTRAP_SESSION_READY
  exec perl "${bootstrap_session_helper}" \
    /bin/sh "$0" "$@"
fi
set -eu

# Bootstrap wrapper for Linux, macOS, Windows/MSYS2, and FreeBSD.
#
# Output layout uses <arch>-<vendor>-<os>-<abi> target triple:
#   build/bootstrap/stage{1,2,3}/<triple>/simple
#
# Triple examples:
#   Linux:   x86_64-unknown-linux-gnu
#   FreeBSD: x86_64-unknown-freebsd-elf

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/bootstrap-from-scratch.sh [options]

Bootstrap wrapper.

Linux / macOS / Windows (Git Bash or MSYS2) / FreeBSD:
  Runs the verified staged bootstrap pipeline using the active runtime binary.

SimpleOS / --target=simpleos-x86_64:
  Runs the host-driven SimpleOS bootstrap target lane and stages guest artifacts
  for the underlying x86_64-simpleos lane.

Output: <output>/stage{1,2,3}/<arch>-<vendor>-<os>-<abi>/simple

Options:
  --backend=<name>   Backend for stage2/stage3/stage4 (default: llvm; cranelift also supported)
  --output=<dir>     Output directory for bootstrap artifacts (default: build/bootstrap)
  --bootstrap-receipt=<path>
                     Canonical non-None typed-reason receipt emitted by
                     `simple build bootstrap`; required before any stage starts
  --validate-bootstrap-receipt
                     Validate authorization and exit without starting a stage
  --full-bootstrap   Rebuild the Rust seed/runtime when missing or stale, then
                     rebuild the pure-Simple stages. Without this flag bootstrap
                     never runs cargo and reuses the existing Rust seed.
  --resume-stage3-from-admitted=<output>
                     Resume only Stage 3 from OUTPUT's frozen admitted Stage 2
                     using a new one-thread recovery transcript/evidence lane.
  --resume-stage4-from-admitted=<output>
                     Continue at Stage 4 from OUTPUT's provenance-admitted
                     Stage 3 without rebuilding or mutating Stage 2/3.
  --pure-simple      Compatibility alias for the default no-Rust rebuild mode.
  --mode=<name>      Pure-Simple build mode: dynload or one-binary
                     (default: dynload; env: SIMPLE_BOOTSTRAP_MODE)
                     SIMPLE_NO_STUB_FALLBACK=1 also makes staged failures fatal
  --full-cli         Relink the full CLI after the staged pure-Simple build
                     (supported on native Linux and macOS hosts).
                     Implied by --deploy and one-binary mode.
  --fresh-cache      Clear the dynload native cache once before rebuilding
  --incremental-unlimited
                     Reuse incremental caches, including one-binary Stage 4,
                     and use every detected host CPU; retain Stage 4
                     structural streaming ownership
  --diagnostic-sweep Continue checking independent .spl files after failures,
                     group all diagnostics, and never build or deploy artifacts
  --diagnostics[=MODE]
                     Opt-in compiler observability: debug or test (default:
                     off; bare --diagnostics selects debug; env:
                     SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE). Both modes imply
                     --progress. Debug also keeps LLVM IR and memory snapshots.
  --diagnostic-root=<path>
                     File or directory selected by --diagnostic-sweep
                     (default: src/compiler; repeatable)
  --diagnostic-child-compiler=<path>
                     Admitted pure-Simple worker used by diagnostic check
                     processes (default: bin/simple; env:
                     SIMPLE_BOOTSTRAP_DIAGNOSTIC_CHILD_COMPILER)
  --clean-release    Final release proof: deploy and test a clean build while
                     clearing every reusable native cache before each batch
  --deploy           Copy the resulting/compiler artifact into bin/simple when supported
  --release          Deploy, then run the release-blocking whole test suite
  --target=<triple>  Target platform (freebsd-x86_64 or simpleos-x86_64)
  --verbose          Accepted for compatibility
  --jobs=<n|full|half|min|auto>
                     Native build workers (default: half CPUs locally, 2 on GitHub Actions)
  --no-mcp           Skip MCP server builds (Stage 5)
  --keep-artifacts   Accepted for compatibility; artifacts are kept
  --no-verify        Accepted for compatibility; hash verification still runs
  --progress[=<path>]
                     Append milestone/liveness samples to PATH (default:
                     <output>/bootstrap-progress.log; env: SIMPLE_BOOTSTRAP_PROGRESS_LOG)
  --progress-interval=<seconds>
                     Liveness sample interval (default: 30; env:
                     SIMPLE_BOOTSTRAP_PROGRESS_INTERVAL)
  --help             Show this help
EOF
}

backend="llvm"
output_dir="build/bootstrap"
deploy=0
build_mcp=1
target=""
verbose=0
jobs=""
pure_simple=0
full_bootstrap=0
resume_stage3_output=""
resume_stage4_output=""
full_cli=0
fresh_cache=0
release_tests=0
diagnostic_sweep=0
diagnostic_roots=""
diagnostic_child_compiler="${SIMPLE_BOOTSTRAP_DIAGNOSTIC_CHILD_COMPILER:-bin/simple}"
diagnostics_mode="${SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE:-off}"
progress_log="${SIMPLE_BOOTSTRAP_PROGRESS_LOG:-}"
progress_interval="${SIMPLE_BOOTSTRAP_PROGRESS_INTERVAL:-30}"
execution_profile="${SIMPLE_BOOTSTRAP_EXECUTION_PROFILE:-incremental}"
bootstrap_mode="${SIMPLE_BOOTSTRAP_MODE:-dynload}"
bootstrap_receipt_path="${SIMPLE_BOOTSTRAP_REASON_RECEIPT:-}"
validate_bootstrap_receipt=0
case "${SIMPLE_NO_STUB_FALLBACK:-0}" in
  1|true|yes|on) strict_bootstrap=1 ;;
  *) strict_bootstrap=0 ;;
esac

while [ "$#" -gt 0 ]; do
  case "$1" in
    --backend=*)
      backend=${1#*=}
      ;;
    --output=*)
      output_dir=${1#*=}
      ;;
    --bootstrap-receipt=*)
      bootstrap_receipt_path=${1#*=}
      ;;
    --validate-bootstrap-receipt)
      validate_bootstrap_receipt=1
      ;;
    --target=*)
      target=${1#*=}
      ;;
    --jobs=*)
      jobs=${1#*=}
      ;;
    --deploy)
      deploy=1
      ;;
    --release)
      release_tests=1
      deploy=1
      ;;
    --full-bootstrap)
      full_bootstrap=1
      ;;
    --resume-stage3-from-admitted=*)
      resume_stage3_output=${1#*=}
      ;;
    --resume-stage4-from-admitted=*)
      resume_stage4_output=${1#*=}
      ;;
    --pure-simple)
      pure_simple=1
      ;;
    --full-cli)
      full_cli=1
      ;;
    --fresh-cache|--no-cache)
      fresh_cache=1
      ;;
    --incremental-unlimited)
      execution_profile=incremental-unlimited
      ;;
    --diagnostic-sweep)
      diagnostic_sweep=1
      ;;
    --diagnostics)
      diagnostics_mode=debug
      ;;
    --diagnostics=*)
      diagnostics_mode=${1#*=}
      ;;
    --diagnostic-root=*)
      diagnostic_root=${1#*=}
      if [ -z "${diagnostic_root}" ]; then
        echo "error: --diagnostic-root requires a path" >&2
        exit 1
      fi
      diagnostic_roots="${diagnostic_roots} --root=${diagnostic_root}"
      ;;
    --diagnostic-child-compiler=*)
      diagnostic_child_compiler=${1#*=}
      if [ -z "${diagnostic_child_compiler}" ]; then
        echo "error: --diagnostic-child-compiler requires a path" >&2
        exit 1
      fi
      ;;
    --clean-release)
      execution_profile=clean-release
      fresh_cache=1
      release_tests=1
      deploy=1
      ;;
    --mode=*)
      bootstrap_mode=${1#*=}
      if [ -z "${bootstrap_mode}" ]; then
        bootstrap_mode=dynload
      fi
      ;;
    --mode)
      shift
      if [ "$#" -eq 0 ]; then
        echo "error: --mode requires dynload or one-binary" >&2
        usage >&2
        exit 1
      fi
      bootstrap_mode=$1
      ;;
    --verbose)
      verbose=1
      ;;
    --no-mcp)
      build_mcp=0
      ;;
    --keep-artifacts|--no-verify)
      ;;
    --progress)
      progress_log=default
      ;;
    --progress=*)
      progress_log=${1#*=}
      [ -n "${progress_log}" ] || progress_log=default
      ;;
    --progress-interval=*)
      progress_interval=${1#*=}
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown option '$1'" >&2
      usage >&2
      exit 1
      ;;
  esac
  shift
done

# This is the common staged-bootstrap boundary, including Windows forwarding
# and admitted Stage 3 resume. A direct/ad-hoc invocation cannot start even
# Stage 1 without the canonical receipt produced by the pure-Simple planner.
if [ -z "${bootstrap_receipt_path}" ] || [ ! -f "${bootstrap_receipt_path}" ]; then
  echo "bootstrap-policy-error: reason-receipt-required; run 'simple build bootstrap --bootstrap-reason=<typed-reason> --bootstrap-receipt=<path>'" >&2
  exit 64
fi
bootstrap_receipt=$(cat -- "${bootstrap_receipt_path}") || {
  echo "bootstrap-policy-error: receipt-read-failed: ${bootstrap_receipt_path}" >&2
  exit 64
}
bootstrap_receipt_target='//bootstrap:stage4'
if [ -n "${resume_stage3_output}" ]; then
  bootstrap_receipt_target='//bootstrap:stage3'
fi
bootstrap_receipt_prefix="simple-bootstrap-receipt-v1|producer=simple-build-planner-v1|target=${bootstrap_receipt_target}|reason="
case "${bootstrap_receipt}" in
  "${bootstrap_receipt_prefix}"*) bootstrap_reason=${bootstrap_receipt#"${bootstrap_receipt_prefix}"} ;;
  *)
    echo "bootstrap-policy-error: malformed-or-untrusted-receipt" >&2
    exit 64
    ;;
esac
case "${bootstrap_reason}" in
  seed-missing|seed-corrupt|seed-target-unsupported|\
  seed-cannot-parse-required-language-feature|\
  seed-cannot-lower-required-compiler-feature|\
  bootstrap-runtime-abi-major-changed|\
  bootstrap-artifact-format-major-changed|\
  bootstrap-core-interface-major-changed|\
  self-host-convergence-check|release-trust-verification|diverse-double-compilation)
    ;;
  *)
    echo "bootstrap-policy-error: typed-reason-required" >&2
    exit 64
    ;;
esac
SIMPLE_BOOTSTRAP_REASON_RECEIPT=${bootstrap_receipt_path}
export SIMPLE_BOOTSTRAP_REASON_RECEIPT
if [ "${validate_bootstrap_receipt}" -eq 1 ]; then
  echo "bootstrap-policy: receipt-valid target=${bootstrap_receipt_target} reason=${bootstrap_reason} execution=not-attempted"
  exit 0
fi

case "${progress_interval}" in
  ''|*[!0-9]*|0)
    echo "error: --progress-interval requires a positive integer" >&2
    exit 1
    ;;
esac

case "${backend}" in
  llvm|llvm-lib|cranelift) ;;
  *)
    echo "error: unsupported bootstrap backend '${backend}' (expected llvm, llvm-lib, or cranelift)" >&2
    exit 1
    ;;
esac

case "${bootstrap_mode}" in
  dynload|one-binary) ;;
  *)
    echo "error: unknown --mode '${bootstrap_mode}' (expected dynload or one-binary)" >&2
    exit 1
    ;;
esac

case "${execution_profile}" in
  incremental|incremental-unlimited|clean-release) ;;
  *)
    echo "error: unknown bootstrap execution profile '${execution_profile}'" >&2
    exit 1
    ;;
esac

if [ -n "${resume_stage3_output}" ]; then
  [ "${full_bootstrap}" -eq 0 ] && [ "${full_cli}" -eq 0 ] &&
    [ "${fresh_cache}" -eq 0 ] && [ "${deploy}" -eq 0 ] &&
    [ "${release_tests}" -eq 0 ] && [ "${diagnostic_sweep}" -eq 0 ] &&
    [ "${diagnostics_mode}" = off ] || {
    echo "error: Stage 3 resume is mutually exclusive with rebuild/deploy/diagnostic options" >&2
    exit 1
  }
  case "${jobs}" in ''|1) ;; *) echo "error: Stage 3 resume permits only --jobs=1" >&2; exit 1 ;; esac
  exec "$(dirname -- "$0")/resume-stage3-from-admitted.sh" "${resume_stage3_output}"
fi

if [ -n "${resume_stage4_output}" ]; then
  [ -z "${resume_stage3_output}" ] && [ "${full_bootstrap}" -eq 0 ] &&
    [ "${fresh_cache}" -eq 0 ] && [ "${release_tests}" -eq 0 ] &&
    [ "${diagnostic_sweep}" -eq 0 ] && [ "${diagnostics_mode}" = off ] &&
    [ "${deploy}" -eq 1 ] || {
    echo "error: Stage 4 resume requires --deploy and excludes rebuild/release/diagnostic options" >&2
    exit 1
  }
  case "${jobs}" in ''|1) jobs=1 ;; *) echo "error: Stage 4 resume permits only --jobs=1" >&2; exit 1 ;; esac
  output_dir=${resume_stage4_output}
  full_cli=1
fi

case "${diagnostics_mode}" in
  off) ;;
  test)
    [ -n "${progress_log}" ] || progress_log=default
    SIMPLE_COMPILER_PHASE_PROFILE=${SIMPLE_COMPILER_PHASE_PROFILE:-1}
    export SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE SIMPLE_COMPILER_PHASE_PROFILE
    ;;
  debug)
    [ -n "${progress_log}" ] || progress_log=default
    SIMPLE_BOOTSTRAP_DIAG=${SIMPLE_BOOTSTRAP_DIAG:-1}
    SIMPLE_COMPILER_TRACE=${SIMPLE_COMPILER_TRACE:-1}
    SIMPLE_COMPILER_PHASE_PROFILE=${SIMPLE_COMPILER_PHASE_PROFILE:-1}
    SIMPLE_KEEP_LLVM_IR=${SIMPLE_KEEP_LLVM_IR:-1}
    SIMPLE_MEM_SNAPSHOT=${SIMPLE_MEM_SNAPSHOT:-1}
    export SIMPLE_BOOTSTRAP_DIAGNOSTICS_MODE SIMPLE_BOOTSTRAP_DIAG
    export SIMPLE_COMPILER_TRACE SIMPLE_COMPILER_PHASE_PROFILE
    export SIMPLE_KEEP_LLVM_IR SIMPLE_MEM_SNAPSHOT
    ;;
  *)
    echo "error: --diagnostics requires off, debug, or test (got '${diagnostics_mode}')" >&2
    exit 1
    ;;
esac

if [ "${pure_simple}" -eq 1 ] && [ "${full_bootstrap}" -eq 1 ]; then
  echo "error: --pure-simple and --full-bootstrap conflict" >&2
  exit 1
fi

if [ "${deploy}" -eq 1 ] || [ "${bootstrap_mode}" = "one-binary" ]; then
  full_cli=1
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "${script_dir}/../.." && pwd)
. "${repo_root}/scripts/bootstrap/bootstrap-cache-policy.shs"
cd "${repo_root}"
BOOTSTRAP_STAGE3_FACADE_PATH=\
"${repo_root}/scripts/check/lib/bootstrap-stage3-provenance.shs"
export BOOTSTRAP_STAGE3_FACADE_PATH
. "${BOOTSTRAP_STAGE3_FACADE_PATH}"
PORTABLE_LOCK_ATOMIC_HELPER_PATH=\
"${repo_root}/scripts/check/lib/portable-hardlink-lock.pl"
export PORTABLE_LOCK_ATOMIC_HELPER_PATH
. "${repo_root}/scripts/check/lib/portable-process-lock.shs"
. "${repo_root}/scripts/bootstrap/bootstrap-authority-wiring.shs"
bootstrap_runtime_authority_path=\
"${repo_root}/src/compiler_rust/target/bootstrap"
bootstrap_script_path="${repo_root}/scripts/bootstrap/bootstrap-from-scratch.sh"
bootstrap_script_sha256_before=$(bootstrap_stage3_hash_file "${bootstrap_script_path}")
bootstrap_provenance_helper="${repo_root}/scripts/check/lib/bootstrap-stage3-provenance.shs"
bootstrap_provenance_helper_sha256_before=$(
  bootstrap_stage3_hash_file "${bootstrap_provenance_helper}"
)
bootstrap_provenance_bundle_fingerprint_before=$(
  bootstrap_stage3_helper_bundle_fingerprint
)
STAGE4_PROVENANCE_HELPER_PATH=\
"${repo_root}/scripts/check/lib/stage4-candidate-provenance.shs"
export STAGE4_PROVENANCE_HELPER_PATH
. "${STAGE4_PROVENANCE_HELPER_PATH}"
RESUME_STAGE4_HELPER_PATH=\
"${repo_root}/scripts/bootstrap/resume-stage4-from-admitted.sh"
. "${RESUME_STAGE4_HELPER_PATH}"
stage4_provenance_helper_sha256_before=$(
  bootstrap_stage3_hash_file "${STAGE4_PROVENANCE_HELPER_PATH}"
)

# Concurrency guard: two bootstraps sharing one ${output_dir} interleave logs
# and race binary writes (observed 2026-07-24: twin stage2 builds truncated
# each other's linked binary to 0 KB, and target/bootstrap/simple was clobbered
# to 0 bytes by the same class of race). Directory-based lock, stale-safe.
bootstrap_lock_handle=
rust_target_lock_handle=
portable_lock_canonical_output "${output_dir}" || {
  echo "error: invalid or inaccessible bootstrap output path: ${output_dir}" >&2
  exit 1
}
output_dir=${PORTABLE_LOCK_CANONICAL_OUTPUT}
bootstrap_lock_root="$(dirname -- "${output_dir}")/.simple-bootstrap-locks"
bootstrap_lock_name="output-$(bootstrap_stage3_args_sha256 "${output_dir}")"
portable_lock_acquire "${bootstrap_lock_root}" "${bootstrap_lock_name}" \
  "${SIMPLE_BOOTSTRAP_LOCK_WAIT_SECONDS:-30}" || {
  echo "error: timed out waiting for bootstrap output ownership: ${output_dir}" >&2
  exit 1
}
bootstrap_lock_handle=${PORTABLE_LOCK_HANDLE}
bootstrap_progress_pid=
deploy_lock_handle=
bootstrap_progress_state=
build_progress_events=
bootstrap_progress_event() {
  [ -n "${build_progress_events}" ] || return 0
  progress_phase=$1
  progress_current=$2
  progress_terminal=${3:-running}
  progress_failed=${4:-unknown}
  if [ "${progress_terminal}" = succeeded ]; then
    printf 'event=build_progress phase=%s unit_kind=tasks done=6 total=6 remaining=0 tasks_done=6 tasks_total=6 tasks_remaining=0 failed=0 cached=unknown current=%s terminal=succeeded\n' \
      "${progress_phase}" "${progress_current}" >>"${build_progress_events}"
  else
    printf 'event=build_progress phase=%s unit_kind=unknown done=unknown total=unknown remaining=unknown tasks_done=unknown tasks_total=unknown tasks_remaining=unknown failed=%s cached=unknown current=%s terminal=%s\n' \
      "${progress_phase}" "${progress_failed}" "${progress_current}" \
      "${progress_terminal}" >>"${build_progress_events}"
  fi
}
bootstrap_progress_mark() {
  [ -n "${progress_log}" ] || return 0
  milestone=$1
  main_log=${2:-}
  {
    echo "milestone=${milestone}"
    echo "main_log=${main_log}"
  } >"${bootstrap_progress_state}.tmp.$$"
  mv "${bootstrap_progress_state}.tmp.$$" "${bootstrap_progress_state}"
  printf 'event=milestone timestamp=%s status=alive pid=%s milestone=%s main_log=%s\n' \
    "$(date +%s)" "$$" "${milestone}" "${main_log:-absent}" >>"${progress_log}"
  case "${milestone}" in
    complete|exit-0)
      bootstrap_progress_event complete complete succeeded 0
      ;;
    exit-*)
      bootstrap_progress_event "${milestone}" failed failed 1
      ;;
    *)
      bootstrap_progress_event "${milestone}" "${milestone}" running unknown
      ;;
  esac
}
bootstrap_cleanup() {
  bootstrap_status=${1:-$?}
  trap - EXIT HUP INT QUIT TERM
  set +e
  resume_stage4_release_continuation_lock
  if [ -n "${progress_log}" ] && [ -n "${bootstrap_progress_state}" ]; then
    bootstrap_progress_mark "exit-${bootstrap_status}" ""
  fi
  if [ -n "${bootstrap_progress_pid}" ]; then
    kill "${bootstrap_progress_pid}" 2>/dev/null || true
    wait "${bootstrap_progress_pid}" 2>/dev/null || true
  fi
  if [ -z "${bootstrap_abnormal_signal:-}" ]; then
    if [ -n "${deploy_lock_handle}" ]; then
      portable_lock_release "${deploy_lock_handle}"
      deploy_lock_handle=
    fi
    if [ -n "${rust_target_lock_handle}" ]; then
      portable_lock_release "${rust_target_lock_handle}"
      rust_target_lock_handle=
    fi
    if [ -n "${bootstrap_lock_handle}" ]; then
      portable_lock_release "${bootstrap_lock_handle}"
      bootstrap_lock_handle=
    fi
  fi
  exit "${bootstrap_status}"
}
bootstrap_signal_exit() {
  bootstrap_abnormal_signal=$1
  bootstrap_signal_status=$2
  trap - HUP INT QUIT TERM
  exit "${bootstrap_signal_status}"
}
bootstrap_abnormal_signal=
trap 'bootstrap_cleanup $?' EXIT
trap 'bootstrap_signal_exit HUP 129' HUP
trap 'bootstrap_signal_exit INT 130' INT
trap 'bootstrap_signal_exit QUIT 131' QUIT
trap 'bootstrap_signal_exit TERM 143' TERM

if [ -n "${progress_log}" ]; then
  [ "${progress_log}" != default ] || progress_log="${output_dir}/bootstrap-progress.log"
  mkdir -p "$(dirname -- "${progress_log}")"
  progress_log="$(CDPATH= cd -- "$(dirname -- "${progress_log}")" && pwd -P)/$(basename -- "${progress_log}")"
  mkdir -p "${output_dir}"
  bootstrap_progress_state="$(CDPATH= cd -- "${output_dir}" && pwd -P)/bootstrap-progress.state"
  build_progress_events="$(CDPATH= cd -- "${output_dir}" && pwd -P)/bootstrap-build-progress.events"
  : >"${progress_log}"
  : >"${build_progress_events}"
  bootstrap_progress_mark starting ""
  sh "${repo_root}/scripts/bootstrap/bootstrap-progress-watch.shs" \
    --pid="$$" --state-file="${bootstrap_progress_state}" \
    --event-file="${build_progress_events}" \
    --progress-log="${progress_log}" --interval="${progress_interval}" &
  bootstrap_progress_pid=$!
fi

normalize_target() {
  case "${1-}" in
    simpleos-x86_64|x86_64-simpleos) echo "simpleos-x86_64" ;;
    *) echo "${1-}" ;;
  esac
}

target=$(normalize_target "${target}")

# ===========================================================================
# Platform detection — <arch>-<vendor>-<os>-<abi> target triple
# ===========================================================================

host_os=$(uname -s 2>/dev/null || echo unknown)

if [ "${full_cli}" -eq 1 ]; then
  case "${host_os}" in
    Linux|Darwin) ;;
    *)
      echo "error: Stage 4 full-CLI capsule preparation requires native Linux or macOS" >&2
      exit 1
      ;;
  esac
fi

# FreeBSD must build inside FreeBSD. Linux hosts use the QEMU verifier, which
# syncs the repository and invokes this same wrapper in the guest.
if [ "${target}" = "freebsd-x86_64" ] && [ "${host_os}" != "FreeBSD" ]; then
  echo "error: FreeBSD bootstrap must run inside FreeBSD." >&2
  echo "  Linux host: sh scripts/check/check-freebsd-bootstrap-qemu.shs --full" >&2
  exit 1
fi

# SimpleOS target-lane dispatch (host-driven bootstrap to staged guest artifacts)
if [ "${target}" = "simpleos-x86_64" ]; then
  simpleos_args="--target=simpleos-x86_64 --build-dir=${output_dir}"
  if [ "${verbose}" -eq 1 ]; then
    simpleos_args="${simpleos_args} --verbose"
  fi
  if [ -n "${jobs}" ]; then
    simpleos_args="${simpleos_args} --jobs=${jobs}"
  fi
  if [ "${deploy}" -eq 1 ]; then
    simpleos_args="${simpleos_args} --package"
  fi
  echo "Bootstrap target lane: simpleos-x86_64"
  echo "  guest lane: x86_64-simpleos"
  exec "${repo_root}/bin/simple" run src/os/port/bootstrap_cross.spl -- ${simpleos_args}
fi

# Shared platform detection
. "${repo_root}/scripts/setup/platform-detect.shs"
PLATFORM="${PLATFORM_TRIPLE}"
arch="${PLATFORM_ARCH}"
os="${PLATFORM_OS}"
echo "Platform: ${PLATFORM}"

exe_suffix=""
archive_prefix="lib"
archive_suffix=".a"
if [ "${os}" = "windows" ]; then
  exe_suffix=".exe"
  case "${SIMPLE_LINKER_FLAVOR:-${PLATFORM_ABI}}" in
    gnu|mingw) windows_linker_abi="gnu" ;;
    msvc) windows_linker_abi="msvc" ;;
    *) echo "error: SIMPLE_LINKER_FLAVOR must be gnu, mingw, or msvc on Windows" >&2; exit 1 ;;
  esac
  if [ "${windows_linker_abi}" != "${PLATFORM_ABI}" ]; then
    echo "error: SIMPLE_LINKER_FLAVOR conflicts with SIMPLE_WINDOWS_ABI=${PLATFORM_ABI}" >&2
    exit 1
  fi
  SIMPLE_WINDOWS_ABI="${PLATFORM_ABI}"
  SIMPLE_LINKER_FLAVOR="${windows_linker_abi}"
  export SIMPLE_WINDOWS_ABI SIMPLE_LINKER_FLAVOR
  if [ "${PLATFORM_ABI}" = "msvc" ]; then
    archive_prefix=""
    archive_suffix=".lib"
  else
    archive_prefix="lib"
    archive_suffix=".a"
  fi
fi

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  elif command -v sha256 >/dev/null 2>&1; then
    sha256 -q "$1"
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | awk '{print $NF}'
  else
    echo "error: no SHA-256 tool found (sha256sum, shasum, sha256, or openssl)" >&2
    return 1
  fi
}

hash_stream() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 | awk '{print $1}'
  elif command -v sha256 >/dev/null 2>&1; then
    sha256 | awk '{print $NF}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 | awk '{print $NF}'
  else
    echo "error: no SHA-256 tool found (sha256sum, shasum, sha256, or openssl)" >&2
    return 1
  fi
}

hash_path_list() {
  while IFS= read -r file; do
    printf '%s  %s\n' "$(hash_file "${file}")" "${file}"
  done
}

run_timeout() {
  timeout_seconds=$1
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout "${timeout_seconds}" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout "${timeout_seconds}" "$@"
  else
    "$@"
  fi
}

run_timeout_kill() {
  timeout_seconds=$1
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout -k 1s "${timeout_seconds}s" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout -k 1s "${timeout_seconds}s" "$@"
  else
    "$@"
  fi
}

absolute_path() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *) printf '%s/%s\n' "${repo_root}" "$1" ;;
  esac
}

if [ -n "${LLVM_PREFIX:-}" ] && [ -d "${LLVM_PREFIX}/bin" ]; then
  case ":${PATH}:" in
    *":${LLVM_PREFIX}/bin:"*) ;;
    *) export PATH="${LLVM_PREFIX}/bin:${PATH}" ;;
  esac
fi

# Bind builds to existing canonical tool directories. Hosted launchers may
# inject duplicate, missing, or symlinked PATH entries (notably Cryptex paths
# on macOS); those are not stable provenance authorities.
bootstrap_canonical_path=
bootstrap_path_old_ifs=$IFS
IFS=:
for bootstrap_path_entry in ${PATH}; do
  IFS=$bootstrap_path_old_ifs
  # Codex launchers prepend per-invocation arg0 shims that can disappear while
  # a long Rust authority build is running. They are not compiler/tool
  # authorities, and admitting them here makes the later before/after tool
  # snapshot fail solely because the launcher cleaned its temporary session.
  case "${bootstrap_path_entry}" in
    */.codex/tmp/arg0/*) IFS=:; continue ;;
  esac
  [ -d "${bootstrap_path_entry}" ] || {
    IFS=:
    continue
  }
  bootstrap_path_entry=$(
    CDPATH= cd -- "${bootstrap_path_entry}" && pwd -P
  ) || exit 1
  case ":${bootstrap_canonical_path}:" in
    *":${bootstrap_path_entry}:"*) ;;
    *)
      bootstrap_canonical_path=\
"${bootstrap_canonical_path:+${bootstrap_canonical_path}:}${bootstrap_path_entry}"
      ;;
  esac
  IFS=:
done
IFS=$bootstrap_path_old_ifs
[ -n "${bootstrap_canonical_path}" ] || {
  echo "error: canonical bootstrap PATH is empty" >&2
  exit 1
}
PATH=${bootstrap_canonical_path}
export PATH

log_dir="${output_dir}/logs/${PLATFORM}"
mkdir -p "${log_dir}"

host_cpus=$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || echo 2)
case "${host_cpus}" in
  ''|*[!0-9]*) host_cpus=2 ;;
esac
case "${jobs}" in
  ""|auto)
    jobs=""
    ;;
  full)
    jobs="${host_cpus}"
    ;;
  half)
    jobs=$((host_cpus / 2))
    if [ "${jobs}" -lt 1 ]; then
      jobs=1
    fi
    ;;
  min|minimal|minimum)
    jobs=1
    ;;
esac
if [ -z "${jobs}" ]; then
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    jobs=2
  elif [ "${execution_profile}" = "clean-release" ]; then
    # A release proof is intentionally full-resource: it must not inherit the
    # conservative incremental scheduler used for developer iteration.
    jobs="${host_cpus}"
  elif [ "${execution_profile}" = "incremental-unlimited" ]; then
    jobs="${host_cpus}"
  else
    jobs=$((host_cpus / 2))
    if [ "${jobs}" -lt 1 ]; then
      jobs=1
    fi
  fi
fi
case "${jobs}" in
  ''|*[!0-9]*|0)
    echo "error: --jobs must be a positive integer" >&2
    exit 1
    ;;
esac
echo "Native build jobs: ${jobs} (host CPUs: ${host_cpus})"
selfhost_jobs="${jobs}"
if [ "${execution_profile}" = "incremental" ] && [ "${selfhost_jobs}" -gt 2 ]; then
  selfhost_jobs=2
fi
echo "Bootstrap execution profile: ${execution_profile} (self-host jobs: ${selfhost_jobs})"

native_cache_dir="${output_dir}/native_cache"
native_cache_stamp="${native_cache_dir}/bootstrap-wide-inputs.sha256"
native_cache_freshened=0

bootstrap_wide_inputs_hash() {
  {
    # Module fingerprints cover source edits, but unchanged modules must also
    # be rebuilt when the compiler/runtime that emits their objects changes.
    printf 'platform=%s backend=%s mode=%s stub_fallback=forbidden\n' "${PLATFORM}" "${backend}" "${bootstrap_mode}"
    printf 'seed-inputs=%s\n' "${seed_inputs_fingerprint:-missing}"
    find src/compiler -name '*.spl' -type f -print 2>/dev/null \
      | LC_ALL=C sort | hash_path_list
    env | LC_ALL=C sort | awk '/^SIMPLE_.*(AOP|MDSOC|WEAV|LOAD|INTERPRET|EXECUTION|LIB|NATIVE_BUILD)/ { print }'
  } | hash_stream
}

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

prepare_native_cache() {
  label=$1
  if [ "${execution_profile}" = "clean-release" ]; then
    echo "  ${label}: clearing native cache (clean-release profile)"
    rm -rf "${native_cache_dir}/"
    mkdir -p "${native_cache_dir}"
    return
  fi
  if bootstrap_cache_force_clear_one_binary \
    "${execution_profile}" "${bootstrap_mode}"; then
    echo "  ${label}: clearing native cache (one-binary mode)"
    rm -rf "${native_cache_dir}/"
    return
  fi

  mkdir -p "${native_cache_dir}"
  current_hash=$(bootstrap_wide_inputs_hash)
  if [ "${fresh_cache}" -eq 1 ] && [ "${native_cache_freshened}" -eq 0 ]; then
    echo "  ${label}: clearing native cache (--fresh-cache)"
    rm -rf "${native_cache_dir}/"
    mkdir -p "${native_cache_dir}"
    printf '%s\n' "${current_hash}" > "${native_cache_stamp}"
    native_cache_freshened=1
    return
  fi
  if [ ! -f "${native_cache_stamp}" ] || [ "$(cat "${native_cache_stamp}" 2>/dev/null)" != "${current_hash}" ]; then
    echo "  ${label}: clearing native cache (platform/backend/AOP build context changed)"
    rm -rf "${native_cache_dir}/"
    mkdir -p "${native_cache_dir}"
    printf '%s\n' "${current_hash}" > "${native_cache_stamp}"
  else
    echo "  ${label}: reusing native cache (${bootstrap_mode} mode)"
  fi
  bootstrap_native_cache_prune "${native_cache_dir}"
}

run_logged() {
  label=$1
  shift
  log_file="${log_dir}/${label}.log"
  {
    echo "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] ${label}"
    echo "cwd: $(pwd)"
    echo "command: $*"
    echo ""
  } >"${log_file}"

  set +e
  "$@" >>"${log_file}" 2>&1
  status=$?
  set -e

  echo "  ${label} log: ${log_file}"
  if [ "${status}" -ne 0 ]; then
    echo "error: ${label} failed with exit ${status}" >&2
    if [ "${status}" -ge 128 ]; then
      signal=$((${status} - 128))
      echo "error: ${label} terminated by signal ${signal}" >&2
    fi
    echo "error: see log ${log_file}" >&2
    exit "${status}"
  fi
}

CANDIDATE_FRONTEND_ROOT=${repo_root}
COMPILER_PROBE_TIMEOUT_SECONDS=5
COMPILER_BUILD_TIMEOUT_SECONDS=60
COMPILER_EXEC_TIMEOUT_SECONDS=5
COMPILER_CHECK_KILL_GRACE_SECONDS=1
. "${repo_root}/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs"

bootstrap_stage_sanity() (
  candidate=$1
  evidence_path=${2:-}
  sanity_home=$3
  sanity_tmpdir=$4
  sanity_path=$5
  for sanity_env_name in $(env | sed 's/=.*//'); do
    case "${sanity_env_name}" in
      ''|[0-9]*|*[!A-Za-z0-9_]*) continue ;;
    esac
    unset "${sanity_env_name}"
  done
  HOME=${sanity_home}
  TMPDIR=${sanity_tmpdir}
  PATH=${sanity_path}
  LC_ALL=C
  LANG=C
  export HOME TMPDIR PATH LC_ALL LANG
  evidence_tmp="${evidence_path:-${TMPDIR:-/tmp}/bootstrap-sanity}.tmp.$$"
  frontend_log="${evidence_tmp}.frontend"
  rm -f "${evidence_tmp}" "${frontend_log}"
  candidate_sha_before=$(bootstrap_stage3_hash_file "${candidate}") || return 1
  version_status=0
  version=$(run_timeout 10 "${candidate}" --version 2>&1) ||
    version_status=$?
  unsupported_status=0
  if unsupported=$(run_timeout 10 "${candidate}" run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl 2>&1); then
    unsupported_status=0
  else
    unsupported_status=$?
  fi
  frontend_status=0
  CANDIDATE_FRONTEND_BACKEND="${backend}" \
    CANDIDATE_FRONTEND_BOOTSTRAP=0 \
    candidate_frontend_smoke "${candidate}" >"${frontend_log}" 2>&1 ||
    frontend_status=$?
  # Second pass under SIMPLE_BOOTSTRAP=1 -- the EXACT configuration Stage 3
  # invokes this candidate in. The single-pass (SIMPLE_BOOTSTRAP=0) gate
  # certified a configuration Stage 3 never uses, and on 2026-08-09 it admitted
  # a Stage-2 binary that could not lex a two-line file, whose failure then ran
  # unbounded (444 MB log / 32 GB RSS). See doc/08_tracking/bug/
  # stage2_binary_lexer_reads_every_source_as_empty_infinite_parser_loop_2026-08-09.md
  frontend_bootstrap_status=0
  if [ "${frontend_status}" -eq 0 ]; then
    CANDIDATE_FRONTEND_BACKEND="${backend}" \
      CANDIDATE_FRONTEND_BOOTSTRAP=1 \
      candidate_frontend_smoke "${candidate}" >>"${frontend_log}" 2>&1 ||
      frontend_bootstrap_status=$?
    frontend_status=${frontend_bootstrap_status}
  fi
  candidate_sha_after=$(bootstrap_stage3_hash_file "${candidate}") || return 1
  sanity_status=fail
  if [ "${version_status}" -eq 0 ] &&
    [ "${version}" = "simple-bootstrap 1.0.0-beta" ] &&
    [ "${unsupported_status}" -eq 1 ] &&
    case "${unsupported}" in *"unknown command 'run'"*) true ;; *) false ;; esac &&
    [ "${frontend_status}" -eq 0 ] &&
    [ "${candidate_sha_before}" = "${candidate_sha_after}" ]; then
    sanity_status=pass
  fi
  if [ -n "${evidence_path}" ]; then
    {
      echo "schema=simple-bootstrap-sanity-evidence-v1"
      echo "status=${sanity_status}"
      echo "candidate_sha256_before=${candidate_sha_before}"
      echo "version_status=${version_status}"
      echo "version_output=${version}"
      echo "unsupported_status=${unsupported_status}"
      printf 'unsupported_output_sha256=%s\n' \
        "$(printf '%s' "${unsupported}" | bootstrap_stage3_hash_stream)"
      echo "frontend_smoke_status=${frontend_status}"
      echo "frontend_smoke_bootstrap_mode_status=${frontend_bootstrap_status}"
      echo "frontend_smoke_output_sha256=$(bootstrap_stage3_hash_file "${frontend_log}")"
      echo "candidate_sha256_after=${candidate_sha_after}"
    } >"${evidence_tmp}" || return 1
    mv "${evidence_tmp}" "${evidence_path}"
  fi
  rm -f "${frontend_log}"
  [ "${sanity_status}" = pass ]
)

bootstrap_native_build_main() {
  compiler=$1
  output=$2
  set -- native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle core-c-bootstrap \
    --source src/compiler --source src/app --source src/lib --source examples/10_tooling \
    --entry-closure \
    --low-memory
  set -- "$@" \
    --threads "${selfhost_jobs}" \
    --cache-dir "${native_cache_dir}" \
    --mode one-binary \
    --entry src/app/cli/main.spl \
    --runtime-path "${bootstrap_runtime_authority_path}" \
    -o "${output}"
  env RUST_LOG="${RUST_LOG:-error}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_BOOTSTRAP_STAGE4=1 \
    SIMPLE_BOOTSTRAP_LOW_MEMORY=1 \
    SIMPLE_STAGE4_STREAMING_SURFACES=1 \
    SIMPLE_NATIVE_ARENA_DECLS=1 \
    SIMPLE_COMPILER_PHASE_PROFILE="${SIMPLE_COMPILER_PHASE_PROFILE:-1}" \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    SIMPLE_NATIVE_BUILD_TARGET="${PLATFORM}" \
    SIMPLE_NATIVE_BUILD_THREADS="${selfhost_jobs}" \
    SIMPLE_NATIVE_BUILD_CACHE_DIR="${native_cache_dir}" \
    SIMPLE_RUNTIME_PATH="${bootstrap_runtime_authority_path}" \
    LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BINARY="$(absolute_path "${compiler}")" \
    "${compiler}" "$@"
}

# ===========================================================================
# Bootstrap pipeline
# ===========================================================================

seed_bin="src/compiler_rust/target/bootstrap/simple${exe_suffix}"
native_all_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_native_all${archive_suffix}"
compiler_backfill_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_compiler_backfill${archive_suffix}"
rust_authority_lock_root="${repo_root}/src/compiler_rust/target/.bootstrap-authority-locks"
rust_authority_generation_root="${repo_root}/src/compiler_rust/target/bootstrap.generations"
rust_authority_current_marker="${repo_root}/src/compiler_rust/target/bootstrap.current.env"
rust_authority_compatibility_path="${repo_root}/src/compiler_rust/target/bootstrap"

bootstrap_acquire_rust_authority() {
  [ -z "${rust_target_lock_handle}" ] || return 0
  portable_lock_acquire "${rust_authority_lock_root}" authority \
    "${SIMPLE_BOOTSTRAP_AUTHORITY_LOCK_WAIT_SECONDS:-120}" || {
    echo "error: timed out waiting for shared Rust authority publication" >&2
    return 1
  }
  rust_target_lock_handle=${PORTABLE_LOCK_HANDLE}
}

bootstrap_release_rust_authority() {
  [ -n "${rust_target_lock_handle}" ] || return 0
  portable_lock_release "${rust_target_lock_handle}" || return 1
  rust_target_lock_handle=
}

if [ "${diagnostic_sweep}" -eq 1 ]; then
  if [ "${deploy}" -eq 1 ] || [ "${release_tests}" -eq 1 ] || [ "${full_cli}" -eq 1 ]; then
    echo "error: --diagnostic-sweep is check-only and cannot deploy, release, or relink" >&2
    exit 1
  fi
  if [ ! -x "${seed_bin}" ]; then
    echo "error: diagnostic sweep requires an existing compiler: ${seed_bin}" >&2
    exit 1
  fi
  # Parser and semantic globals cannot safely recover from an arbitrary broken
  # module in-process. Independent compiler processes are therefore the owner
  # boundary; stable per-file cache directories isolate concurrent writers.
  # This mode has no output-artifact or deployment path.
  # shellcheck disable=SC2086
  if sh scripts/check/bootstrap-diagnostic-sweep.shs \
    --compiler="${seed_bin}" --child-compiler="${diagnostic_child_compiler}" \
    --cache-dir="${output_dir}/diagnostic-cache" \
    --jobs="${jobs}" ${diagnostic_roots}; then
    exit 0
  else
    diagnostic_status=$?
    exit "${diagnostic_status}"
  fi
fi

# Detect stale seed OR stale runtime library by CONTENT, not mtime.
#
# The previous check used `find -newer` (mtime). jj/git operations (reconcile,
# checkout, working-copy snapshots) routinely bump .rs mtimes WITHOUT changing
# content, which made every bootstrap spuriously recompile ~11 Rust crates
# (~5 min of pure waste; measured 2026-06-14: 286s, 0 content changes).
#
# seed_inputs_hash fingerprints everything that determines the seed binary +
# runtime library: all Rust sources, every Cargo.toml, Cargo.lock, the build
# profile/backend/features, and the rustc version. A stamp file beside the seed
# records the fingerprint of the inputs the current seed was built from; we
# rebuild only when the fingerprint differs (or is missing) — never on mtime
# churn. Any doubt (missing stamp, hash failure → empty mismatch) rebuilds: a
# stale seed would silently miscompile, which is worse than a slow build.
seed_stamp="${seed_bin}.inputs.sha256"
seed_fingerprint_tmp="${output_dir}/rust-authority-fingerprint-tmp"
seed_fingerprint_error_manifest=\
"${output_dir}/rust-authority-fingerprint-error.manifest"
seed_fingerprint_error=\
"${output_dir}/rust-authority-fingerprint-error.log"
seed_inputs_hash() {
  seed_fingerprint_phase=$1
  bootstrap_authority_seed_inputs_fingerprint \
    "${seed_fingerprint_phase}" "${seed_fingerprint_tmp}" \
    "${seed_fingerprint_error_manifest}" "${seed_fingerprint_error}" \
    "${repo_root}" \
    "${backend}" "${llvm_features}" "${PATH}" "${PLATFORM}"
}
seed_stale=0
rust_rebuilt=0
compiler_backfill_rebuilt=0
if [ -e "${rust_authority_current_marker}.transaction" ]; then
  bootstrap_acquire_rust_authority || exit 1
  bootstrap_authority_recover_or_refuse "${full_bootstrap}" \
    "${rust_authority_generation_root}" "${rust_authority_current_marker}" \
    "${rust_authority_compatibility_path}" \
    "${rust_target_lock_handle}" || {
    if [ "${full_bootstrap}" -eq 0 ]; then
      echo "error: Rust authority publication is incomplete; run --full-bootstrap to recover" >&2
    else
      echo "error: full bootstrap could not recover Rust authority publication" >&2
    fi
    exit 1
  }
  bootstrap_release_rust_authority || exit 1
fi
# (content-hash staleness gate runs below, after backend/llvm_features settle)

# Detect LLVM 18 availability for LLVM backends.
llvm_features=""
if [ "${backend}" = "llvm-lib" ] || [ "${backend}" = "llvm" ]; then
  # LLVM is resolved once by the shared platform interface
  # (scripts/setup/platform-detect.shs, sourced above), which also exports the
  # LLVM_SYS_<major>0_PREFIX used by the Rust build and the runtime's LLVM path.
  if [ "${LLVM_FOUND:-0}" = "1" ]; then
    echo "LLVM ${LLVM_VERSION} found: ${LLVM_PREFIX} (lib: ${LLVM_LIB})"
    llvm_features="--features llvm"
    # macOS needs LIBRARY_PATH for zstd and other Homebrew libs
    if [ "${host_os}" = "Darwin" ]; then
      brew_prefix="$(brew --prefix 2>/dev/null || true)"
      if [ -n "${brew_prefix}" ]; then
        export HOMEBREW_PREFIX="${brew_prefix}"
        export LIBRARY_PATH="${LIBRARY_PATH:+${LIBRARY_PATH}:}${brew_prefix}/lib"
      fi
      export SDKROOT="${SDKROOT:-$(xcrun --show-sdk-path 2>/dev/null || true)}"
    fi
  else
    echo "error: LLVM not found (shared platform detection: scripts/setup/platform-detect.shs, versions: ${LLVM_VERSIONS:-18})" >&2
    echo "error: install LLVM or select --backend=cranelift explicitly" >&2
    exit 1
  fi
fi

# Content-hash staleness gate (see seed_inputs_hash above). Runs here so the
# backend/features are final before they enter the fingerprint. If the seed or
# runtime library is missing, the cargo branch below rebuilds regardless.
seed_inputs_fingerprint=not-used-by-admitted-stage4-resume
if [ -z "${resume_stage4_output}" ]; then
  bootstrap_progress_mark fingerprint ""
  seed_inputs_fingerprint=$(seed_inputs_hash pre) || {
    echo "error: failed to fingerprint Rust seed inputs" >&2
    exit 1
  }
fi
if [ -z "${resume_stage4_output}" ] && [ -x "${seed_bin}" ] && [ -f "${native_all_lib}" ]; then
  if ! bootstrap_stage3_verify_seed_stamp "${seed_stamp}" \
    "${seed_inputs_fingerprint}" "${seed_bin}" "${native_all_lib}" \
    "${compiler_backfill_lib}"; then
    seed_stale=1
    if [ "${full_bootstrap}" -eq 1 ]; then
      echo "Seed/runtime stale (Rust source content changed since last build). Full bootstrap will rebuild Rust."
    else
      echo "WARNING: Seed/runtime stale, but this is not --full-bootstrap; reusing the existing Rust seed."
    fi
  else
    echo "Seed/runtime current (input content hash matches); skipping Rust rebuild."
  fi
fi

if [ "${full_bootstrap}" -eq 1 ]; then
  rust_authority_root="${output_dir}/rust-authority-${seed_inputs_fingerprint}"
  rust_authority_target="${rust_authority_root}/target"
  rust_authority_profile_dir="${rust_authority_target}/${PLATFORM}/bootstrap"
  rust_authority_home="${rust_authority_root}/home"
  rust_authority_cargo_home="${rust_authority_root}/cargo-home"
  rust_authority_tmp="${rust_authority_root}/tmp"
  rust_toolchain_authority=$(
    bootstrap_stage3_resolve_rust_toolchain "${repo_root}" "${PATH}"
  ) || {
    echo "error: could not resolve canonical Rust toolchain" >&2
    exit 1
  }
  rust_sysroot=$(
    printf '%s\n' "${rust_toolchain_authority}" |
      sed -n 's/^rust-sysroot=//p'
  )
  rustc_abs=$(
    printf '%s\n' "${rust_toolchain_authority}" |
      sed -n 's/^rustc-path=//p'
  )
  cargo_abs=$(
    printf '%s\n' "${rust_toolchain_authority}" |
      sed -n 's/^cargo-path=//p'
  )
  [ -x "${rustc_abs}" ] && [ -x "${cargo_abs}" ] || {
    echo "error: Rust toolchain binaries missing under sysroot: ${rust_sysroot}" >&2
    exit 1
  }
  mingw_linker="${CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER:-gcc}"
  mingw_cc="${CC_x86_64_pc_windows_gnu:-gcc}"
  mingw_ar="${AR_x86_64_pc_windows_gnu:-ar}"
  cc_abs=$(bootstrap_stage3_target_c_compiler "${PLATFORM}") || {
    echo "error: no C compiler found for Rust authority target ${PLATFORM}" >&2
    exit 1
  }
  windows_include="${INCLUDE:-}"
  windows_lib="${LIB:-}"
  windows_libpath="${LIBPATH:-}"
  windows_system_root="${SystemRoot:-}"
  windows_temp="${TEMP:-${rust_authority_tmp}}"
  rust_llvm_authority=$(
    bootstrap_stage3_resolve_llvm_build_authority \
      "${PATH}" "${llvm_features}"
  ) || {
    echo "error: could not resolve deterministic LLVM build authority" >&2
    exit 1
  }
  rust_llvm_status=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-build-status=//p'
  )
  rust_llvm_major=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-major=//p'
  )
  rust_llvm_prefix=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-prefix=//p'
  )
  rust_llvm_sdkroot=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-sdkroot=//p'
  )
  rust_llvm_homebrew_prefix=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-homebrew-prefix=//p'
  )
  rust_llvm_library_path=$(
    printf '%s\n' "${rust_llvm_authority}" |
      sed -n 's/^llvm-library-path=//p'
  )
fi

rust_authority_workspace_prepared=0
prepare_rust_authority_workspace() {
  if [ "${rust_authority_workspace_prepared}" -eq 1 ]; then
    return 0
  fi

  rm -rf "${rust_authority_root}"
  mkdir -p "${rust_authority_target}" "${rust_authority_home}" \
    "${rust_authority_cargo_home}" "${rust_authority_tmp}"
  vendored_sources_absolute=$(
    CDPATH= cd -- "${repo_root}/src/compiler_rust/vendor" && pwd -P
  )
  if [ "${os}" = "windows" ]; then
    vendored_sources_absolute=$(cygpath -m "${vendored_sources_absolute}") || {
      echo "error: could not convert vendored Cargo source path for Windows" >&2
      exit 1
    }
  fi
  cargo_authority_config="${rust_authority_cargo_home}/config.toml"
  awk -v vendored_sources="${vendored_sources_absolute}" '
    {
      config_line = $0
      sub(/\r$/, "", config_line)
    }
    config_line == "directory = \"vendor\"" {
      print "directory = \"" vendored_sources "\""
      replaced += 1
      next
    }
    { print }
    END { if (replaced != 1) exit 1 }
  ' "${repo_root}/src/compiler_rust/.cargo/config.toml" \
    >"${cargo_authority_config}" || {
    echo "error: could not create private offline Cargo configuration" >&2
    exit 1
  }
  rust_authority_workspace_prepared=1
}

run_rust_authority_cargo() {
  rust_authority_log=$1
  rust_authority_lto=$2
  shift 2
  if [ -n "${progress_log}" ]; then
    bootstrap_progress_mark "rust-${rust_authority_log}" \
      "$(absolute_path "${log_dir}/${rust_authority_log}.log")"
  fi
  if [ "${os}" = "windows" ]; then
    set -- "$@" --target "${PLATFORM}"
  fi
  prepare_rust_authority_workspace
  if [ "${rust_llvm_status:-disabled}" = enabled ]; then
    if [ "${rust_authority_lto}" = off ]; then
      run_logged "${rust_authority_log}" env -i \
        HOME="$(absolute_path "${rust_authority_home}")" \
        CARGO_HOME="$(absolute_path "${rust_authority_cargo_home}")" \
        CARGO_TARGET_DIR="$(absolute_path "${rust_authority_target}")" \
        TMPDIR="$(absolute_path "${rust_authority_tmp}")" PATH="${PATH}" \
        RUSTC="${rustc_abs}" CC="${cc_abs}" LC_ALL=C LANG=C \
        CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER="${mingw_linker}" \
        CC_x86_64_pc_windows_gnu="${mingw_cc}" \
        AR_x86_64_pc_windows_gnu="${mingw_ar}" \
        INCLUDE="${windows_include}" LIB="${windows_lib}" \
        LIBPATH="${windows_libpath}" SystemRoot="${windows_system_root}" \
        TEMP="${windows_temp}" \
        "LLVM_SYS_${rust_llvm_major}0_PREFIX=${rust_llvm_prefix}" \
        "HOMEBREW_PREFIX=${rust_llvm_homebrew_prefix}" \
        "LIBRARY_PATH=${rust_llvm_library_path}" \
        "SDKROOT=${rust_llvm_sdkroot}" CARGO_PROFILE_BOOTSTRAP_LTO=off \
        "${cargo_abs}" "$@"
    else
      run_logged "${rust_authority_log}" env -i \
        HOME="$(absolute_path "${rust_authority_home}")" \
        CARGO_HOME="$(absolute_path "${rust_authority_cargo_home}")" \
        CARGO_TARGET_DIR="$(absolute_path "${rust_authority_target}")" \
        TMPDIR="$(absolute_path "${rust_authority_tmp}")" PATH="${PATH}" \
        RUSTC="${rustc_abs}" CC="${cc_abs}" LC_ALL=C LANG=C \
        CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER="${mingw_linker}" \
        CC_x86_64_pc_windows_gnu="${mingw_cc}" \
        AR_x86_64_pc_windows_gnu="${mingw_ar}" \
        INCLUDE="${windows_include}" LIB="${windows_lib}" \
        LIBPATH="${windows_libpath}" SystemRoot="${windows_system_root}" \
        TEMP="${windows_temp}" \
        "LLVM_SYS_${rust_llvm_major}0_PREFIX=${rust_llvm_prefix}" \
        "HOMEBREW_PREFIX=${rust_llvm_homebrew_prefix}" \
        "LIBRARY_PATH=${rust_llvm_library_path}" \
        "SDKROOT=${rust_llvm_sdkroot}" \
        "${cargo_abs}" "$@"
    fi
  elif [ "${rust_authority_lto}" = off ]; then
    run_logged "${rust_authority_log}" env -i \
      HOME="$(absolute_path "${rust_authority_home}")" \
      CARGO_HOME="$(absolute_path "${rust_authority_cargo_home}")" \
      CARGO_TARGET_DIR="$(absolute_path "${rust_authority_target}")" \
      TMPDIR="$(absolute_path "${rust_authority_tmp}")" PATH="${PATH}" \
      RUSTC="${rustc_abs}" CC="${cc_abs}" LC_ALL=C LANG=C \
      CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER="${mingw_linker}" \
      CC_x86_64_pc_windows_gnu="${mingw_cc}" \
      AR_x86_64_pc_windows_gnu="${mingw_ar}" \
      INCLUDE="${windows_include}" LIB="${windows_lib}" \
      LIBPATH="${windows_libpath}" SystemRoot="${windows_system_root}" \
      TEMP="${windows_temp}" \
      CARGO_PROFILE_BOOTSTRAP_LTO=off "${cargo_abs}" "$@"
  else
    run_logged "${rust_authority_log}" env -i \
      HOME="$(absolute_path "${rust_authority_home}")" \
      CARGO_HOME="$(absolute_path "${rust_authority_cargo_home}")" \
      CARGO_TARGET_DIR="$(absolute_path "${rust_authority_target}")" \
      TMPDIR="$(absolute_path "${rust_authority_tmp}")" PATH="${PATH}" \
      RUSTC="${rustc_abs}" CC="${cc_abs}" LC_ALL=C LANG=C \
      CARGO_TARGET_X86_64_PC_WINDOWS_GNU_LINKER="${mingw_linker}" \
      CC_x86_64_pc_windows_gnu="${mingw_cc}" \
      AR_x86_64_pc_windows_gnu="${mingw_ar}" \
      INCLUDE="${windows_include}" LIB="${windows_lib}" \
      LIBPATH="${windows_libpath}" SystemRoot="${windows_system_root}" \
      TEMP="${windows_temp}" \
      "${cargo_abs}" "$@"
  fi
}

if [ "${full_bootstrap}" -eq 0 ] && [ -z "${resume_stage4_output}" ]; then
  # Default/pure-Simple rebuild: reuse the existing Rust seed and runtime
  # library, never invoke cargo. Whether the existing seed CAN build the changed
  # pure-Simple is proven by Stage 2 below: if the new .spl needs a Rust feature
  # the seed lacks, Stage 2 fails — rerun with --full-bootstrap.
  if [ ! -x "${seed_bin}" ] || [ ! -f "${native_all_lib}" ]; then
    echo "error: bootstrap needs an existing Rust seed and runtime library:" >&2
    echo "  seed:    ${seed_bin}" >&2
    echo "  runtime: ${native_all_lib}" >&2
    echo "Normal bootstrap does not rebuild Rust. Re-run with --full-bootstrap to build them." >&2
    exit 1
  fi
  if [ "${full_cli}" -eq 1 ] && [ ! -f "${compiler_backfill_lib}" ]; then
    echo "error: full CLI bootstrap needs the compiler backfill archive: ${compiler_backfill_lib}" >&2
    echo "Re-run with --full-bootstrap to build it." >&2
    exit 1
  fi
  if [ "${full_cli}" -eq 1 ] && [ "${seed_stale}" -eq 1 ]; then
    echo "error: full CLI bootstrap refuses a stale compiler backfill; re-run with --full-bootstrap" >&2
    exit 1
  fi
  if [ "${seed_stale}" -eq 1 ]; then
    echo "WARNING: Rust sources changed; reusing the existing seed because --full-bootstrap was not given."
  fi
  echo "Pure-Simple mode: ${bootstrap_mode}; reusing Rust seed, rebuilding only pure-Simple stages."
elif [ "${full_bootstrap}" -eq 1 ] && bootstrap_stage3_rust_tuple_requires_complete_rebuild \
  "${seed_bin}" "${native_all_lib}" "${compiler_backfill_lib}" \
  "${seed_stale}"; then
  echo "Building Rust seed compiler + runtime library..."
  # Split into two cargo invocations to defeat feature unification:
  # `simple-native-all` enables `driver-hooks` on `simple-runtime`, which gates
  # out the `not(driver-hooks)` `#[no_mangle]` def of rt_cli_run_file. Building
  # both packages in a single `cargo build -p A -p B` call unifies features,
  # leaving the `simple-driver` bin with an undefined `rt_cli_run_file` symbol
  # (the C symbol is provided by `simple-native-all`, which the seed bin does
  # not link). Separate invocations keep simple-runtime's feature set per-bin.
  run_rust_authority_cargo rust-seed-build default \
    build --locked --offline \
    --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap \
    --target "${PLATFORM}" -p simple-driver ${llvm_features}
  run_rust_authority_cargo rust-native-all-build default \
    build --locked --offline \
    --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap \
    --target "${PLATFORM}" -p simple-native-all ${llvm_features}
  # Rebuild simple-runtime LAST with LTO off so deps/libsimple_runtime.a holds
  # machine-code symbol definitions. Under the bootstrap profile's thin-LTO the
  # rlib members export symbols only inside embedded `__bitcode` sections, which
  # the stage4 `-r` capsule link cannot LTO-compile — every runtime root then
  # audits as "0 definitions". The last cargo invocation wins the deps/ archive
  # slot, so this must stay after the driver and native-all builds.
  run_rust_authority_cargo rust-runtime-nolto-build off \
    build --locked --offline \
    --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap \
    --target "${PLATFORM}" -p simple-runtime --features runtime-symbol-table
  rust_rebuilt=1
fi

if [ "${full_bootstrap}" -eq 1 ] \
   && { [ ! -f "${compiler_backfill_lib}" ] || [ "${seed_stale}" -eq 1 ] || [ "${rust_rebuilt}" -eq 1 ]; }; then
  run_rust_authority_cargo rust-compiler-backfill-build default \
    build --locked --offline \
    --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap \
    --target "${PLATFORM}" -p simple-compiler-backfill
  compiler_backfill_rebuilt=1
fi
if [ "${rust_rebuilt}" -eq 1 ] || [ "${compiler_backfill_rebuilt}" -eq 1 ]; then
  seed_inputs_fingerprint_after=$(seed_inputs_hash post) || {
    echo "error: failed to re-fingerprint Rust seed inputs after Cargo" >&2
    exit 1
  }
  if [ "${seed_inputs_fingerprint_after}" != "${seed_inputs_fingerprint}" ]; then
    echo "error: Rust inputs changed during full bootstrap; refusing to publish a stale seed" >&2
    exit 1
  fi
  seed_inputs_fingerprint="${seed_inputs_fingerprint_after}"
  rust_generation_nonce=$(od -An -N16 -tx1 /dev/urandom 2>/dev/null | tr -d ' \n')
  case "${rust_generation_nonce}" in
    [0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f][0-9a-f]) ;;
    *) echo "error: could not generate Rust authority nonce" >&2; exit 1 ;;
  esac
  bootstrap_stage3_prepare_seed_generation \
    "${rust_authority_profile_dir}" "${rust_authority_generation_root}" \
    "${seed_inputs_fingerprint}" "simple${exe_suffix}" \
    "${archive_prefix}simple_native_all${archive_suffix}" \
    "${archive_prefix}simple_compiler_backfill${archive_suffix}" \
    "${rust_generation_nonce}" || {
    echo "error: could not prepare immutable Rust authority generation" >&2
    exit 1
  }
  bootstrap_acquire_rust_authority || exit 1
  seed_inputs_fingerprint_commit=$(seed_inputs_hash commit) || {
    echo "error: failed to fingerprint Rust inputs before authority commit" >&2
    exit 1
  }
  [ "${seed_inputs_fingerprint_commit}" = "${seed_inputs_fingerprint}" ] || {
    echo "error: Rust inputs changed while waiting to publish authority" >&2
    exit 1
  }
  bootstrap_stage3_publish_seed_generation \
    "${BOOTSTRAP_STAGE3_PREPARED_STAGING}" \
    "${BOOTSTRAP_STAGE3_PREPARED_GENERATION}" \
    "${rust_authority_current_marker}" "${seed_inputs_fingerprint}" \
    "${BOOTSTRAP_STAGE3_PREPARED_HASH}" \
    "${seed_inputs_fingerprint_commit}" \
    "${rust_authority_compatibility_path}" || {
    echo "error: could not commit immutable Rust authority generation" >&2
    exit 1
  }
  bootstrap_stage3_resolve_committed_seed \
    "${rust_authority_generation_root}" \
    "${rust_authority_current_marker}" || {
    echo "error: committed Rust authority generation failed verification" >&2
    exit 1
  }
  seed_bin="src/compiler_rust/target/bootstrap/simple${exe_suffix}"
  native_all_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_native_all${archive_suffix}"
  compiler_backfill_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_compiler_backfill${archive_suffix}"
  seed_stamp="${seed_bin}.inputs.sha256"
fi

# Force manual bootstrap — ensures SIMPLE_RUNTIME_PATH is used for linking
# The full CLI `build bootstrap` command doesn't forward the runtime path
can_full_bootstrap=0

export SIMPLE_RUNTIME_PATH="${bootstrap_runtime_authority_path}"
export SIMPLE_BOOTSTRAP=1
echo "Running bootstrap pipeline..."
echo "  runtime:  ${SIMPLE_RUNTIME_PATH}"
echo "  platform: ${PLATFORM}"
echo "  backend:  ${backend}"
echo "  ps-mode:  ${bootstrap_mode}"
echo "  diagnose: ${diagnostics_mode}"
echo "  output:   ${output_dir}"
if [ "${full_bootstrap}" -eq 1 ]; then
  echo "  rust:     full-bootstrap enabled; seed/runtime may be rebuilt"
else
  echo "  rust:     seed/runtime reuse only; cargo disabled"
fi

if [ -n "${resume_stage4_output}" ]; then
  echo "  mode:     admitted Stage 3 → Stage 4 continuation"
  stage3_provenance_dir="${output_dir}/stage3/${PLATFORM}"
  stage3_provenance_manifest="${stage3_provenance_dir}/provenance.env"
  resume_stage4_prepare "${output_dir}" "${repo_root}" "${PLATFORM}" \
    "${bootstrap_receipt_path}" || exit 1
  stage2="${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}"
  stage3="${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}"
  stage3_ok=1
elif [ "${can_full_bootstrap}" -eq 1 ]; then
  # Full CLI available — use high-level staged bootstrap
  echo "  mode:     full CLI (build bootstrap)"
  RUST_LOG="${RUST_LOG:-error}" \
    SIMPLE_RUNTIME_PATH="${bootstrap_runtime_authority_path}" \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    "${seed_bin}" run src/app/cli/main.spl build bootstrap "--backend=${backend}" "--output=${output_dir}"
else
  # Bootstrap-only or missing — manual staged bootstrap via seed
  echo "  mode:     manual (seed → bootstrap_main → bootstrap_main)"
  if [ ! -x "${seed_bin}" ]; then
    echo "error: Rust seed required for manual bootstrap (${seed_bin})" >&2
    echo "Run: scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap" >&2
    exit 1
  fi

  # Capture the complete source authority before either staged compiler runs.
  # The manifest is emitted only after an identical post-Stage-3 snapshot.
  stage3_provenance_dir="${output_dir}/stage3/${PLATFORM}"
  stage3_provenance_manifest="${stage3_provenance_dir}/provenance.env"
  stage3_source_before="${stage3_provenance_dir}/source-inputs-before.txt"
  stage3_source_after="${stage3_provenance_dir}/source-inputs-after.txt"
  stage3_git_before="${stage3_provenance_dir}/git-state-before.env"
  stage3_git_after="${stage3_provenance_dir}/git-state-after.env"
  stage2_command_transcript="${stage3_provenance_dir}/stage2-command.transcript"
  stage3_command_transcript="${stage3_provenance_dir}/stage3-command.transcript"
  stage2_sanity_evidence="${stage3_provenance_dir}/stage2-sanity.env"
  stage3_sanity_evidence="${stage3_provenance_dir}/stage3-sanity.env"
  stage2_provenance_cache="${stage3_provenance_dir}/stage2-native-cache"
  stage3_provenance_cache="${stage3_provenance_dir}/stage3-native-cache"
  stage2_provenance_home="${stage3_provenance_dir}/stage2-home"
  stage2_provenance_tmp="${stage3_provenance_dir}/stage2-tmp"
  stage3_provenance_home="${stage3_provenance_dir}/stage3-home"
  stage3_provenance_tmp="${stage3_provenance_dir}/stage3-tmp"
  stage2_admitted_dir="${stage3_provenance_dir}/stage2-admitted"
  stage2_admitted_bin="${stage2_admitted_dir}/simple${exe_suffix}"
  stage2_runtime_authority="${stage3_provenance_dir}/stage2-runtime-authority"
  runtime_origin_before="${stage3_provenance_dir}/runtime-origin-before.txt"
  runtime_origin_after="${stage3_provenance_dir}/runtime-origin-after.txt"
  runtime_admitted_snapshot="${stage3_provenance_dir}/runtime-admitted.txt"
  tool_authority_before="${stage3_provenance_dir}/tool-authority-before.txt"
  tool_authority_after="${stage3_provenance_dir}/tool-authority-after.txt"
  mkdir -p "${stage3_provenance_dir}"
  # A previous fail-closed run may leave its admitted authority deliberately
  # frozen (directories 0500, files 0400/0500). Thaw only this private output
  # tree before replacing it; source/runtime authorities remain untouched.
  chmod -R u+w "${stage3_provenance_dir}" || {
    echo "error: could not thaw previous Stage 3 provenance output" >&2
    exit 1
  }
  rm -f "${stage3_provenance_manifest}" \
    "${stage3_source_before}" "${stage3_source_after}" \
    "${stage3_git_before}" "${stage3_git_after}" \
    "${stage2_command_transcript}" "${stage3_command_transcript}" \
    "${stage2_sanity_evidence}" "${stage3_sanity_evidence}"
  rm -rf "${stage2_provenance_home}" "${stage2_provenance_tmp}" \
    "${stage3_provenance_home}" "${stage3_provenance_tmp}" \
    "${stage2_admitted_dir}" "${stage2_runtime_authority}"
  # Stage 2/3 native-build caches are content-hash keyed by the pure-Simple
  # driver itself (driver_native_sources_fingerprint scopes each cache entry
  # under the loaded source set's combined hash — see
  # src/compiler/80.driver/driver_aot_native_output.spl), so an unchanged
  # source tree naturally misses on any real change and never serves a stale
  # object. Unconditionally wiping them here defeated ALL cross-run
  # incrementality even when nothing changed. Preserve them by default;
  # --fresh-cache/--clean-release still forces a clean rebuild.
  if [ "${fresh_cache}" -eq 1 ] || [ "${execution_profile}" = "clean-release" ]; then
    echo "  provenance: clearing stage2/stage3 native caches (--fresh-cache/--clean-release)"
    rm -rf "${stage2_provenance_cache}" "${stage3_provenance_cache}"
  else
    # Preserved caches still need a reaper: scope dirs are mint-once and
    # nothing else collects them now that the unconditional wipe is gone.
    bootstrap_native_cache_prune "${stage2_provenance_cache}"
    bootstrap_native_cache_prune "${stage3_provenance_cache}"
  fi
  mkdir -p "${stage2_provenance_home}" "${stage2_provenance_tmp}" \
    "${stage3_provenance_home}" "${stage3_provenance_tmp}"
  bootstrap_acquire_rust_authority || exit 1
  bootstrap_authority_require_owned_lock "${rust_target_lock_handle}" || {
    echo "error: Rust authority lock ownership was lost before legacy normalization" >&2
    exit 1
  }
  runtime_origin_absolute=$(bootstrap_stage3_physical_directory \
    "$(absolute_path src/compiler_rust/target/bootstrap)") || {
    echo "error: missing Rust runtime authority" >&2
    exit 1
  }
  runtime_bootstrap_self_link="${runtime_origin_absolute}/bootstrap"
  if [ -L "${runtime_bootstrap_self_link}" ]; then
    runtime_bootstrap_self_target=$(readlink "${runtime_bootstrap_self_link}") ||
      exit 1
    case "${runtime_bootstrap_self_target}" in
      /*)
        runtime_bootstrap_self_target=$(
          CDPATH= cd -- "${runtime_bootstrap_self_target}" && pwd -P
        ) || exit 1
        ;;
      *)
        runtime_bootstrap_self_target=$(
          CDPATH= cd -- \
            "${runtime_origin_absolute}/${runtime_bootstrap_self_target}" &&
            pwd -P
        ) || exit 1
        ;;
    esac
    [ "${runtime_bootstrap_self_target}" = "${runtime_origin_absolute}" ] || {
      echo "error: unexpected Rust runtime authority symlink" >&2
      exit 1
    }
    rm -f "${runtime_bootstrap_self_link}"
  fi
  runtime_compiler_archive_link="${runtime_origin_absolute}/libsimple_compiler.a"
  if [ -L "${runtime_compiler_archive_link}" ]; then
    runtime_compiler_archive_target=$(readlink \
      "${runtime_compiler_archive_link}") || exit 1
    [ "${runtime_compiler_archive_target}" = "deps/libsimple_compiler.a" ] || {
      echo "error: unexpected Rust compiler archive authority symlink" >&2
      exit 1
    }
    [ -f "${runtime_origin_absolute}/${runtime_compiler_archive_target}" ] || {
      echo "error: missing Rust compiler archive authority target" >&2
      exit 1
    }
    bootstrap_authority_materialize_legacy_file \
      "${rust_target_lock_handle}" "${runtime_compiler_archive_link}" || {
      echo "error: could not materialize Rust compiler archive under authority lock" >&2
      exit 1
    }
  fi
  if [ ! -f "${rust_authority_current_marker}" ]; then
    bootstrap_stage3_verify_seed_stamp "${seed_stamp}" \
      "${seed_inputs_fingerprint}" "${seed_bin}" "${native_all_lib}" \
      "${compiler_backfill_lib}" || {
      echo "error: markerless legacy Rust authority is incomplete or stale" >&2
      echo "Run with --full-bootstrap to publish a complete immutable tuple." >&2
      exit 1
    }
    legacy_generation_nonce=$(od -An -N16 -tx1 /dev/urandom 2>/dev/null | tr -d ' \n')
    legacy_observed_fingerprint=$(seed_inputs_hash commit) || exit 1
    bootstrap_authority_migrate_complete_legacy \
      "${runtime_origin_absolute}" "${rust_authority_generation_root}" \
      "${rust_authority_current_marker}" \
      "${rust_authority_compatibility_path}" \
      "${seed_inputs_fingerprint}" \
      "simple${exe_suffix}" \
      "${archive_prefix}simple_native_all${archive_suffix}" \
      "${archive_prefix}simple_compiler_backfill${archive_suffix}" \
      "${legacy_generation_nonce}" "${rust_target_lock_handle}" \
      "${legacy_observed_fingerprint}" || {
      echo "error: complete legacy Rust authority migration failed" >&2
      exit 1
    }
    runtime_origin_absolute=${BOOTSTRAP_STAGE3_COMMITTED_AUTHORITY}
  fi
  if [ -f "${rust_authority_current_marker}" ]; then
    bootstrap_stage3_resolve_committed_seed \
      "${rust_authority_generation_root}" \
      "${rust_authority_current_marker}" || {
      echo "error: committed Rust authority is not admissible" >&2
      exit 1
    }
    runtime_origin_absolute=${BOOTSTRAP_STAGE3_COMMITTED_AUTHORITY}
  fi
  bootstrap_stage3_directory_snapshot \
    "$(absolute_path "${runtime_origin_before}")" \
    "${runtime_origin_absolute}" || {
    echo "error: could not snapshot Rust runtime authority" >&2
    exit 1
  }
  bootstrap_stage3_copy_authority "${runtime_origin_absolute}" \
    "$(absolute_path "${stage2_runtime_authority}")" || {
    echo "error: could not freeze Stage 2 runtime authority" >&2
    exit 1
  }
  bootstrap_stage3_directory_snapshot \
    "$(absolute_path "${runtime_origin_after}")" \
    "${runtime_origin_absolute}" || exit 1
  bootstrap_stage3_directory_snapshot \
    "$(absolute_path "${runtime_admitted_snapshot}")" \
    "$(absolute_path "${stage2_runtime_authority}")" || exit 1
  cmp -s "${runtime_origin_before}" "${runtime_origin_after}" &&
    cmp -s "${runtime_origin_after}" "${runtime_admitted_snapshot}" || {
    echo "error: Rust runtime authority changed during private admission" >&2
    exit 1
  }
  bootstrap_release_rust_authority || {
    echo "error: could not release Rust authority after private admission" >&2
    exit 1
  }
  bootstrap_authority_pin_stage4 \
    "$(absolute_path "${stage2_runtime_authority}")" \
    "simple${exe_suffix}" \
    "${archive_prefix}simple_native_all${archive_suffix}" \
    "${archive_prefix}simple_compiler_backfill${archive_suffix}" || {
    echo "error: private admitted Rust authority is incomplete" >&2
    exit 1
  }
  stage_runtime_absolute=${BOOTSTRAP_STAGE4_RUNTIME_PATH}
  stage2_seed_absolute=${BOOTSTRAP_STAGE4_SEED}
  seed_bin=${BOOTSTRAP_STAGE4_SEED}
  native_all_lib=${BOOTSTRAP_STAGE4_NATIVE_ALL}
  compiler_backfill_lib=${BOOTSTRAP_STAGE4_BACKFILL}
  seed_stamp="${seed_bin}.inputs.sha256"
  SIMPLE_RUNTIME_PATH=${stage_runtime_absolute}
  bootstrap_runtime_authority_path=${stage_runtime_absolute}
  export SIMPLE_RUNTIME_PATH
  bootstrap_stage3_tool_authority_snapshot \
    "$(absolute_path "${tool_authority_before}")" "${PATH}" \
    "${repo_root}" || {
    echo "error: could not bind bootstrap tool authority" >&2
    exit 1
  }
  bootstrap_stage3_git_state "${repo_root}" "${stage3_git_before}" || {
    echo "error: could not bind Stage 3 git HEAD/dirty state" >&2
    exit 1
  }
  bootstrap_stage3_source_snapshot "${stage3_source_before}" "${repo_root}" || {
    echo "error: could not snapshot Stage 3 source authority" >&2
    exit 1
  }

  # Stage 2: seed compiles bootstrap_main.spl
  # Stage 2 uses the configured backend; LLVM is the default and Cranelift is
  # an explicit supported alternative.
  mkdir -p "${output_dir}/stage2/${PLATFORM}"
  echo "Stage 2: seed → bootstrap_main.spl"
  bootstrap_progress_mark stage2 "$(absolute_path "${log_dir}/stage2-native-build.log")"
  mkdir -p "${stage2_provenance_cache}"
  # Stage 2 failure is reported before Stage 3; no later stage may claim it.
  # the self-hosting frontend now fails closed instead of linking a ret-0 stub
  # (doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md), so a
  # stage-2 build error must not abort the whole pipeline.
  stage2_bin="$(absolute_path \
    "${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}")"
  stage3_bin="$(absolute_path \
    "${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}")"
  native_verbose_arg=""
  if [ "${verbose}" -eq 1 ]; then
    native_verbose_arg="--verbose"
  fi
  stage_build_rust_log="${RUST_LOG:-error}"
  stage2_seed_absolute="$(absolute_path \
    "${stage2_runtime_authority}/simple${exe_suffix}")"
  stage2_output_absolute="${stage2_bin}"
  stage3_output_absolute="${stage3_bin}"
  stage2_admitted_absolute="$(absolute_path "${stage2_admitted_bin}")"
  stage_runtime_absolute="$(absolute_path "${stage2_runtime_authority}")"
  stage2_cache_absolute="$(absolute_path "${stage2_provenance_cache}")"
  stage3_cache_absolute="$(absolute_path "${stage3_provenance_cache}")"
  stage2_home_absolute="$(absolute_path "${stage2_provenance_home}")"
  stage2_tmp_absolute="$(absolute_path "${stage2_provenance_tmp}")"
  stage3_home_absolute="$(absolute_path "${stage3_provenance_home}")"
  stage3_tmp_absolute="$(absolute_path "${stage3_provenance_tmp}")"
  stage_build_path="${PATH:?PATH is required}"
  case "${stage_build_path}" in
    /*) ;;
    *) echo "error: bootstrap PATH must contain absolute entries only" >&2; exit 1 ;;
  esac
  if printf '%s\n' "${stage_build_path}" | grep -Eq '(^|:)([^/]|$)'; then
    echo "error: bootstrap PATH must contain absolute entries only" >&2
    exit 1
  fi
  bootstrap_link_library_path=""
  bootstrap_link_compat_sha256=absent
  if [ "${os}" = "linux" ]; then
    bootstrap_unwind_link_name=$(
      "${cc_abs:-cc}" -print-file-name=libunwind.so 2>/dev/null || true
    )
    bootstrap_unwind_runtime=$(
      "${cc_abs:-cc}" -print-file-name=libunwind.so.8 2>/dev/null || true
    )
    if [ "${bootstrap_unwind_link_name}" = "libunwind.so" ] &&
       [ -f "${bootstrap_unwind_runtime}" ]; then
      bootstrap_link_compat_dir="${stage3_provenance_dir}/link-compat"
      rm -rf "${bootstrap_link_compat_dir}"
      mkdir -p "${bootstrap_link_compat_dir}"
      cp -pL "${bootstrap_unwind_runtime}" \
        "${bootstrap_link_compat_dir}/libunwind.so"
      bootstrap_link_library_path=$(
        absolute_path "${bootstrap_link_compat_dir}"
      )
      bootstrap_link_compat_sha256=$(
        bootstrap_stage3_hash_file \
          "${bootstrap_link_compat_dir}/libunwind.so"
      ) || exit 1
    fi
  fi
  stage2_build_args_sha256=$(
    bootstrap_stage3_args_sha256 \
      "RUST_LOG=${stage_build_rust_log}" \
      "LIBRARY_PATH=${bootstrap_link_library_path}" \
      "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=${bootstrap_link_compat_sha256}" \
      "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
      "SIMPLE_NATIVE_BUILD_RUST=1" \
      "SIMPLE_NO_STUB_FALLBACK=1" \
      "SIMPLE_BUILD_PROGRESS_EVENTS=${build_progress_events}" \
      "SIMPLE_BINARY=${stage2_seed_absolute}" \
      native-build --target "${PLATFORM}" --backend "${backend}" \
      --runtime-bundle core-c-bootstrap \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure --threads "${jobs}" --cache-dir "${stage2_cache_absolute}" \
      ${native_verbose_arg} \
      --mode "${bootstrap_mode}" --entry src/app/cli/bootstrap_main.spl \
      --runtime-path "${stage_runtime_absolute}" \
      -o "${stage2_bin}"
  )
  stage3_build_args_sha256=$(
    bootstrap_stage3_args_sha256 \
      "RUST_LOG=${stage_build_rust_log}" \
      "LIBRARY_PATH=${bootstrap_link_library_path}" \
      "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=${bootstrap_link_compat_sha256}" \
      "SIMPLE_BOOTSTRAP=1" "SIMPLE_NO_DEPRECATED_WARNINGS=1" \
      "SIMPLE_NATIVE_ARENA_DECLS=1" \
      "SIMPLE_NO_STUB_FALLBACK=1" \
      "SIMPLE_BUILD_PROGRESS_EVENTS=${build_progress_events}" \
      "LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1" \
      "SIMPLE_NATIVE_BUILD_TARGET=${PLATFORM}" \
      "SIMPLE_NATIVE_BUILD_THREADS=${selfhost_jobs}" \
      "SIMPLE_NATIVE_BUILD_CACHE_DIR=${stage3_cache_absolute}" \
      "SIMPLE_RUNTIME_PATH=${stage_runtime_absolute}" \
      "SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap" \
      "SIMPLE_BINARY=${stage2_admitted_absolute}" \
      native-build --target "${PLATFORM}" --backend "${backend}" \
      --runtime-bundle core-c-bootstrap \
      --threads "${selfhost_jobs}" \
      --cache-dir "${stage3_cache_absolute}" --mode "${bootstrap_mode}" \
      --runtime-path "${stage_runtime_absolute}" \
      -o "${stage3_bin}" src/app/cli/bootstrap_main.spl
  )
  rm -f "${stage2_bin}" "${stage3_bin}"
  bootstrap_stage3_directory_snapshot \
    "${stage3_provenance_dir}/runtime-before-stage2.txt" \
    "${stage_runtime_absolute}" || exit 1
  cmp -s "${runtime_admitted_snapshot}" \
    "${stage3_provenance_dir}/runtime-before-stage2.txt" || exit 1
  set +e
  bootstrap_stage3_run_transcribed \
    "$(absolute_path "${stage2_command_transcript}")" "${repo_root}" \
    "$(absolute_path "${log_dir}/stage2-native-build.log")" \
    "${stage2_home_absolute}" "${stage2_tmp_absolute}" "${stage_build_path}" \
    RUST_LOG="${stage_build_rust_log}" \
    LIBRARY_PATH="${bootstrap_link_library_path}" \
    SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256="${bootstrap_link_compat_sha256}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_NATIVE_BUILD_RUST=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    SIMPLE_BINARY="${stage2_seed_absolute}" -- \
    "${stage2_seed_absolute}" native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle core-c-bootstrap \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
    --threads "${jobs}" \
    ${native_verbose_arg} \
    --cache-dir "${stage2_cache_absolute}" \
    --mode "${bootstrap_mode}" \
    --entry src/app/cli/bootstrap_main.spl \
    --runtime-path "${stage_runtime_absolute}" \
    -o "${stage2_bin}"
  stage2_status=$?
  set -e
  bootstrap_stage3_directory_snapshot \
    "${stage3_provenance_dir}/runtime-after-stage2.txt" \
    "${stage_runtime_absolute}" || exit 1
  cmp -s "${runtime_admitted_snapshot}" \
    "${stage3_provenance_dir}/runtime-after-stage2.txt" || {
    echo "error: frozen runtime authority changed during Stage 2" >&2
    exit 1
  }
  echo "  stage2-native-build log: ${log_dir}/stage2-native-build.log"
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    echo "  Stage 2: running bootstrap compiler sanity"
    if ! bootstrap_stage_sanity "${stage2_bin}" \
      "$(absolute_path "${stage2_sanity_evidence}")" \
      "${stage2_home_absolute}" "${stage2_tmp_absolute}" \
      "${stage_build_path}"; then
      echo "error: Stage 2 bootstrap compiler sanity failed" >&2
      stage2_status=2
      rm -f "${stage2_bin}"
    fi
  fi
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    stage2_origin_sha_before=$(bootstrap_stage3_hash_file "${stage2_bin}")
    mkdir -p "${stage2_admitted_dir}"
    cp -p "${stage2_bin}" "${stage2_admitted_bin}"
    chmod 500 "${stage2_admitted_dir}" "${stage2_admitted_bin}"
    stage2_origin_sha_after=$(bootstrap_stage3_hash_file "${stage2_bin}")
    [ "${stage2_origin_sha_before}" = "${stage2_origin_sha_after}" ] &&
      [ "${stage2_origin_sha_before}" = \
        "$(bootstrap_stage3_hash_file "${stage2_admitted_bin}")" ] || {
      echo "error: Stage 2 compiler changed during private admission" >&2
      exit 1
    }
  fi
  if [ "${stage2_status}" -ne 0 ]; then
    if [ "${strict_bootstrap}" -eq 1 ]; then
      echo "error: strict bootstrap stage2 failed (exit ${stage2_status}); refusing seed fallback" >&2
      exit "${stage2_status}"
    fi
    echo "  warning: stage2 native-build failed (exit ${stage2_status}); Stage 3/full CLI unavailable" >&2
    echo "  warning: see doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md" >&2
  fi

  # Stage 3: stage2 recompiles bootstrap_main.spl (self-host verification)
  # Note: Stage3 is optional — the stage2 binary may lack features needed for
  # pure in-process self-hosting. When Stage 3 fails, the wrapper stops before
  # Stage 4.
  mkdir -p "${output_dir}/stage3/${PLATFORM}"
  echo "Stage 3: stage2 → bootstrap_main.spl (self-host)"
  bootstrap_progress_mark stage3 "$(absolute_path "${log_dir}/stage3-native-build.log")"
  # See the cache-preservation note above (~line 1300): this cache is
  # content-hash scoped by the driver itself, so keep it across runs unless
  # a clean rebuild was explicitly requested.
  if [ "${fresh_cache}" -eq 1 ] || [ "${execution_profile}" = "clean-release" ]; then
    rm -rf "${stage3_provenance_cache}"
  fi
  mkdir -p "${stage3_provenance_cache}"

  stage3_ok=0
  rm -f "${stage3_bin}"
  stage2_admitted_sha_before_stage3=absent
  if [ "${stage2_status}" -eq 0 ]; then
    stage2_admitted_sha_before_stage3=$(
      bootstrap_stage3_hash_file "${stage2_admitted_absolute}"
    ) || exit 1
    bootstrap_stage3_directory_snapshot \
      "${stage3_provenance_dir}/runtime-before-stage3.txt" \
      "${stage_runtime_absolute}" || exit 1
    cmp -s "${runtime_admitted_snapshot}" \
      "${stage3_provenance_dir}/runtime-before-stage3.txt" || exit 1
  fi
  # STAGE 3 MUST USE THE BARE POSITIONAL `.spl` SHAPE. Do NOT add `--entry`,
  # `--entry-closure`, or `--source` here (see
  # doc/08_tracking/bug/stage3_entry_flag_delegates_to_rust_seed_2026-08-04.md).
  # `run_native_build_bootstrap` (src/app/cli/bootstrap_main.spl) routes to the
  # pure-Simple in-process CompilerDriver ONLY for a single `.spl` positional
  # with no `--source`. An explicit `--entry` outside the Stage 4 allowlist, or
  # ANY `--source`, falls through to `run_rt_native_build` -> the Rust seed FFI,
  # which silently turns the self-host verification into a second seed build.
  # The positional branch already seeds SIMPLE_NATIVE_BUILD_ENTRY and
  # SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=0, so entry-closure discovery still
  # happens -- inside the self-hosted driver, which is the point of Stage 3.
  # Stage 2 above is a seed build by design and keeps its --entry/--source form.
  set +e
  [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ] && \
  bootstrap_stage3_run_transcribed \
    "$(absolute_path "${stage3_command_transcript}")" "${repo_root}" \
    "$(absolute_path "${log_dir}/stage3-native-build.log")" \
    "${stage3_home_absolute}" "${stage3_tmp_absolute}" "${stage_build_path}" \
    RUST_LOG="${stage_build_rust_log}" \
    LIBRARY_PATH="${bootstrap_link_library_path}" \
    SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256="${bootstrap_link_compat_sha256}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_NATIVE_ARENA_DECLS=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
    LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
    SIMPLE_NATIVE_BUILD_TARGET="${PLATFORM}" \
    SIMPLE_NATIVE_BUILD_THREADS="${selfhost_jobs}" \
    SIMPLE_NATIVE_BUILD_CACHE_DIR="${stage3_cache_absolute}" \
    SIMPLE_RUNTIME_PATH="${stage_runtime_absolute}" \
    SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap \
    SIMPLE_BINARY="${stage2_admitted_absolute}" -- \
    "${stage2_admitted_absolute}" native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle core-c-bootstrap \
    --threads "${selfhost_jobs}" \
    --cache-dir "${stage3_cache_absolute}" \
    --mode "${bootstrap_mode}" \
    --runtime-path "${stage_runtime_absolute}" \
    -o "${stage3_bin}" src/app/cli/bootstrap_main.spl
  stage3_status=$?
  set -e
  # Stage 3 self-host provenance gate (fail-closed).
  # `Build complete: N compiled, M cached, K failed` and `Linked: ... via
  # clang++` are emitted ONLY by src/compiler_rust/native_all/src/lib.rs. The
  # pure-Simple in-process CompilerDriver path prints neither -- it is silent on
  # success and prints `error: in-process native-build: ...` on failure. So
  # either marker in the Stage 3 log proves the Rust seed, not the Stage 2
  # self-hosted compiler, produced the Stage 3 binary. Without this gate the
  # delegation is completely silent and Stage 3 reads as a successful
  # self-host while actually being a second seed build.
  stage3_provenance_log="${log_dir}/stage3-native-build.log"
  if [ -f "${stage3_provenance_log}" ] && \
    grep -qE '^(Build complete: [0-9]+ compiled|Linked: .* via clang)' \
      "${stage3_provenance_log}"; then
    echo "error: Stage 3 was built by the Rust seed (rt_native_build), not the" >&2
    echo "       Stage 2 self-hosted compiler -- the self-host verification is" >&2
    echo "       vacuous. The Stage 3 native-build args must be the bare" >&2
    echo "       positional .spl form (no --entry / --entry-closure / --source)." >&2
    echo "       See doc/08_tracking/bug/stage3_entry_flag_delegates_to_rust_seed_2026-08-04.md" >&2
    echo "       Evidence: ${stage3_provenance_log}" >&2
    exit 1
  fi
  if [ "${stage2_admitted_sha_before_stage3}" != absent ]; then
    [ "${stage2_admitted_sha_before_stage3}" = \
      "$(bootstrap_stage3_hash_file "${stage2_admitted_absolute}")" ] || {
      echo "error: admitted Stage 2 compiler changed during Stage 3" >&2
      exit 1
    }
    bootstrap_stage3_directory_snapshot \
      "${stage3_provenance_dir}/runtime-after-stage3.txt" \
      "${stage_runtime_absolute}" || exit 1
    cmp -s "${runtime_admitted_snapshot}" \
      "${stage3_provenance_dir}/runtime-after-stage3.txt" || {
      echo "error: frozen runtime authority changed during Stage 3" >&2
      exit 1
    }
  fi

  echo "  stage3-native-build log: ${log_dir}/stage3-native-build.log"
  if [ "${stage3_status}" -eq 0 ] && [ -x "${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}" ]; then
    if bootstrap_stage_sanity "${stage3_bin}" \
      "$(absolute_path "${stage3_sanity_evidence}")" \
      "${stage3_home_absolute}" "${stage3_tmp_absolute}" \
      "${stage_build_path}"; then
      stage3_ok=1
      echo "  Stage 3 succeeded and passed bootstrap compiler sanity"
    else
      stage3_status=2
      rm -f "${stage3_bin}"
      echo "error: Stage 3 bootstrap compiler sanity failed" >&2
    fi
  fi
  if [ "${stage3_ok}" -ne 1 ]; then
    if [ "${strict_bootstrap}" -eq 1 ]; then
      echo "error: strict bootstrap stage3 failed; refusing seed fallback" >&2
      if [ "${stage3_status}" -ne 0 ]; then
        exit "${stage3_status}"
      fi
      exit 2
    fi
    if [ "${stage3_status}" -eq 0 ]; then
      echo "  warning: stage3 self-host produced no executable; Stage 4 unavailable"
    else
      echo "  warning: stage3 self-host failed (exit ${stage3_status}); Stage 4 unavailable"
    fi
  else
    bootstrap_stage3_tool_authority_snapshot \
      "$(absolute_path "${tool_authority_after}")" "${PATH}" \
      "${repo_root}" || exit 1
    cmp -s "${tool_authority_before}" "${tool_authority_after}" || {
      echo "error: bootstrap tool authority changed during Stage 2/3" >&2
      exit 1
    }
    bootstrap_stage3_git_state "${repo_root}" "${stage3_git_after}" || {
      echo "error: could not re-bind Stage 3 git HEAD/dirty state" >&2
      exit 1
    }
    bootstrap_stage3_source_snapshot "${stage3_source_after}" "${repo_root}" || {
      echo "error: could not snapshot Stage 3 source authority after build" >&2
      exit 1
    }
    BSTAGE3_ROOT="${repo_root}"
    BSTAGE3_MANIFEST="$(absolute_path "${stage3_provenance_manifest}")"
    BSTAGE3_PLATFORM="${PLATFORM}"
    BSTAGE3_BACKEND="${backend}"
    BSTAGE3_MODE="${bootstrap_mode}"
    BSTAGE3_SEED="${stage2_seed_absolute}"
    BSTAGE3_SEED_STAMP="${stage2_seed_absolute}.inputs.sha256"
    BSTAGE3_NATIVE_ALL="${stage_runtime_absolute}/${archive_prefix}simple_native_all${archive_suffix}"
    BSTAGE3_BACKFILL="${stage_runtime_absolute}/${archive_prefix}simple_compiler_backfill${archive_suffix}"
    BSTAGE3_RUNTIME_ORIGIN_BEFORE="$(absolute_path "${runtime_origin_before}")"
    BSTAGE3_RUNTIME_ORIGIN_AFTER="$(absolute_path "${runtime_origin_after}")"
    BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT="$(absolute_path "${runtime_admitted_snapshot}")"
    BSTAGE3_TOOL_AUTHORITY="$(absolute_path "${tool_authority_after}")"
    BSTAGE3_STAGE2="$(absolute_path "${stage2_bin}")"
    BSTAGE3_STAGE2_ADMITTED="${stage2_admitted_absolute}"
    BSTAGE3_STAGE3="$(absolute_path "${stage3_bin}")"
    BSTAGE3_SOURCE_BEFORE="$(absolute_path "${stage3_source_before}")"
    BSTAGE3_SOURCE_AFTER="$(absolute_path "${stage3_source_after}")"
    BSTAGE3_STAGE2_LOG="$(absolute_path "${log_dir}/stage2-native-build.log")"
    BSTAGE3_STAGE3_LOG="$(absolute_path "${log_dir}/stage3-native-build.log")"
    BSTAGE3_STAGE2_ARGS_SHA256="${stage2_build_args_sha256}"
    BSTAGE3_STAGE3_ARGS_SHA256="${stage3_build_args_sha256}"
    BSTAGE3_STAGE2_THREADS="${jobs}"
    BSTAGE3_STAGE3_THREADS="${selfhost_jobs}"
    BSTAGE3_STAGE2_CACHE_DIR="${stage2_cache_absolute}"
    BSTAGE3_STAGE3_CACHE_DIR="${stage3_cache_absolute}"
    BSTAGE3_RUNTIME_PATH="${stage_runtime_absolute}"
    BSTAGE3_STAGE2_COMMAND_OUTPUT="${stage2_bin}"
    BSTAGE3_STAGE3_COMMAND_OUTPUT="${stage3_bin}"
    BSTAGE3_BOOTSTRAP_SCRIPT="${bootstrap_script_path}"
    BSTAGE3_HELPER="${bootstrap_provenance_helper}"
    BSTAGE3_HELPER_SHA256_BEFORE="${bootstrap_provenance_helper_sha256_before}"
    BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE=\
"${bootstrap_provenance_bundle_fingerprint_before}"
    BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE="${bootstrap_script_sha256_before}"
    BSTAGE3_SEED_INPUTS_FINGERPRINT="${seed_inputs_fingerprint}"
    BSTAGE3_SEED_FEATURES="${llvm_features}"
    BSTAGE3_GIT_BEFORE="$(absolute_path "${stage3_git_before}")"
    BSTAGE3_GIT_AFTER="$(absolute_path "${stage3_git_after}")"
    BSTAGE3_STAGE2_TRANSCRIPT="$(absolute_path "${stage2_command_transcript}")"
    BSTAGE3_STAGE3_TRANSCRIPT="$(absolute_path "${stage3_command_transcript}")"
    BSTAGE3_STAGE2_SANITY="$(absolute_path "${stage2_sanity_evidence}")"
    BSTAGE3_STAGE3_SANITY="$(absolute_path "${stage3_sanity_evidence}")"
    BSTAGE3_LOCK="$(absolute_path "${bootstrap_lock}")"
    BSTAGE3_RUST_LOG="${stage_build_rust_log}"
    export BSTAGE3_ROOT BSTAGE3_MANIFEST BSTAGE3_PLATFORM BSTAGE3_BACKEND \
      BSTAGE3_MODE BSTAGE3_SEED BSTAGE3_NATIVE_ALL BSTAGE3_BACKFILL \
      BSTAGE3_RUNTIME_ORIGIN_BEFORE BSTAGE3_RUNTIME_ORIGIN_AFTER \
      BSTAGE3_RUNTIME_ADMITTED_SNAPSHOT \
      BSTAGE3_TOOL_AUTHORITY \
      BSTAGE3_SEED_STAMP BSTAGE3_HELPER BSTAGE3_HELPER_SHA256_BEFORE \
      BSTAGE3_HELPER_BUNDLE_FINGERPRINT_BEFORE \
      BSTAGE3_STAGE2 BSTAGE3_STAGE2_ADMITTED BSTAGE3_STAGE3 \
      BSTAGE3_SOURCE_BEFORE \
      BSTAGE3_SOURCE_AFTER BSTAGE3_STAGE2_LOG BSTAGE3_STAGE3_LOG \
      BSTAGE3_STAGE2_ARGS_SHA256 BSTAGE3_STAGE3_ARGS_SHA256 \
      BSTAGE3_STAGE2_THREADS BSTAGE3_STAGE3_THREADS \
      BSTAGE3_STAGE2_CACHE_DIR BSTAGE3_STAGE3_CACHE_DIR \
      BSTAGE3_RUNTIME_PATH BSTAGE3_STAGE2_COMMAND_OUTPUT \
      BSTAGE3_STAGE3_COMMAND_OUTPUT \
      BSTAGE3_BOOTSTRAP_SCRIPT BSTAGE3_BOOTSTRAP_SCRIPT_SHA256_BEFORE \
      BSTAGE3_SEED_INPUTS_FINGERPRINT BSTAGE3_SEED_FEATURES \
      BSTAGE3_GIT_BEFORE BSTAGE3_GIT_AFTER \
      BSTAGE3_STAGE2_TRANSCRIPT BSTAGE3_STAGE3_TRANSCRIPT \
      BSTAGE3_STAGE2_SANITY BSTAGE3_STAGE3_SANITY BSTAGE3_LOCK \
      BSTAGE3_RUST_LOG
    bootstrap_stage3_write_manifest || {
      echo "error: refusing Stage 3 without canonical provenance" >&2
      exit 1
    }
    echo "  Stage 3 provenance: ${stage3_provenance_manifest}"
  fi

  stage2_capability_ok=0
  stage2_capability_bin="${output_dir}/stage2-capability-${PLATFORM}${exe_suffix}"
  stage2_capability_cache="${output_dir}/stage2-capability-cache"
  rm -f "${stage2_capability_bin}"
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    set +e
    env SIMPLE_BOOTSTRAP=1 \
      SIMPLE_NO_DEPRECATED_WARNINGS=1 \
      "${stage2_bin}" native-build \
      --target "${PLATFORM}" \
      --backend "${backend}" \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure \
      --threads 1 \
      --cache-dir "${stage2_capability_cache}" \
      --mode "${bootstrap_mode}" \
      --entry test/04_smoke/windows_native_hello.spl \
      --runtime-path "${stage_runtime_absolute}" \
      -o "${stage2_capability_bin}" \
      >"${log_dir}/stage2-capability.log" 2>&1
    stage2_capability_status=$?
    set -e
    if [ "${stage2_capability_status}" -eq 0 ] && [ -x "${stage2_capability_bin}" ]; then
      if stage2_capability_output="$(run_timeout 30 "${stage2_capability_bin}" 2>/dev/null)"; then
        if [ "${stage2_capability_output}" = "windows native hello" ]; then
          stage2_capability_ok=1
          echo "  Stage 2 native-build capability passed"
        fi
      fi
    fi
  fi
  if [ "${stage2_capability_ok}" -ne 1 ]; then
    echo "  warning: Stage 2 native-build capability failed; using seed for stage 4" >&2
    echo "  warning: see ${log_dir}/stage2-capability.log" >&2
  fi
fi

# Locate stage outputs — check new layout first, fall back to flat
if [ -x "${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}" ]; then
  stage2="${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}"
  stage3="${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}"
elif [ -x "${output_dir}/simple_stage2" ]; then
  stage2="${output_dir}/simple_stage2"
  stage3="${output_dir}/simple_stage3"
else
  stage2=""
  stage3=""
fi

if [ ! -x "${stage2}" ]; then
  echo "warning: stage2 binary was not produced; Stage 3/full CLI unavailable" >&2
  stage3_ok=0
fi

# Decide which compiler to use for stage 4
stage4_is_seed=0
if [ "${stage3_ok:-0}" -eq 1 ] && [ -x "${stage3}" ]; then
  hash2=$(hash_file "${stage2}")
  hash3=$(hash_file "${stage3}")
  echo "stage2 sha256: ${hash2}"
  echo "stage3 sha256: ${hash3}"
  if [ "${hash2}" != "${hash3}" ]; then
    echo "warning: stage2 and stage3 hashes differ (expected when runtime is embedded)"
    echo "  Using verified Stage 3 for stage 4"
  else
    echo "Bootstrap verification passed."
  fi
  stage_for_build="${stage3}"
else
  echo "Stage 3 unavailable — no provenance-verified compiler for Stage 4"
  stage_for_build=""
  stage4_is_seed=1
fi

# Fast iteration stops after the pure-Simple dynload stages. Relinking the
# complete CLI is explicit because it is the dominant cost and is unnecessary
# for ordinary compiler/app/lib edits that are consumed through dynload caches.
if [ "${full_cli}" -eq 0 ]; then
  echo "Pure-Simple dynload build complete; full CLI relink skipped."
  echo "  cache: ${native_cache_dir}"
  echo "  use --full-cli, --deploy, or --mode=one-binary to relink"
  if [ "${stage3_ok:-0}" -eq 0 ]; then
    exit 2
  fi
  exit 0
fi

if [ "${stage4_is_seed}" -eq 1 ]; then
  echo "error: full CLI build requires a verified pure-Simple stage2/stage3 compiler; refusing seed fallback" >&2
  exit 2
fi
# ===========================================================================
# Stage 4: Compile full CLI (main.spl) with verified bootstrap compiler
# ===========================================================================

echo "Stage 4: compiling full CLI (main.spl) with bootstrap compiler..."
bootstrap_progress_mark stage4-fingerprint ""
full_dir="${output_dir}/full/${PLATFORM}"
mkdir -p "${full_dir}"
stage4_source_revision_before="$(stage4_source_revision "${repo_root}")" || {
  echo "error: could not fingerprint Stage 4 source authority" >&2
  exit 1
}
prepare_native_cache stage4
stage4_parent="$(bootstrap_stage3_canonical_file "$(absolute_path "${stage_for_build}")")" || {
  echo "error: Stage 4 parent compiler path is not canonical" >&2
  exit 1
}
full_bin="$(bootstrap_stage3_canonical_path "$(absolute_path "${full_dir}/simple${exe_suffix}")")" || {
  echo "error: Stage 4 output path is not canonical" >&2
  exit 1
}
rm -f "${full_bin}" "${full_bin}.provenance.env"
bootstrap_progress_mark stage4 "$(absolute_path "${log_dir}/stage4-native-build.log")"
run_logged stage4-native-build bootstrap_native_build_main \
  "${stage4_parent}" "${full_bin}"

if grep -Eq '\[stmt_get_tag\] OOB|\[flat-bridge\] missing (stmt|expr) tag' "${log_dir}/stage4-native-build.log"; then
  echo "error: Stage 4 emitted stale flat-AST index diagnostics" >&2
  exit 1
fi

if [ ! -x "${full_bin}" ]; then
  echo "error: failed to compile full CLI binary from main.spl" >&2
  exit 1
fi

bootstrap_progress_mark stage4-smoke "$(absolute_path "${log_dir}/stage4-native-build.log")"
if [ -z "${resume_stage4_output}" ]; then
  install -m755 "${seed_bin}" "${full_dir}/simple_seed${exe_suffix}"
fi

stage4_smoke="$(run_timeout 30 "${full_bin}" -c 'print(1+1)' 2>/dev/null)"
if [ "${stage4_smoke}" != "2" ]; then
  echo "error: stage4 binary failed smoke test (-c 'print(1+1)' -> '${stage4_smoke}')" >&2
  exit 1
fi

# `-c` can succeed by delegating to the sibling Rust seed even when the newly
# linked full CLI cannot read or compile source files itself. MCP/LSP startup
# needs the latter, so reject such candidates before deployment.
if ! run_timeout 60 env SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
    "${full_bin}" check src/app/cli/bootstrap_main.spl >/dev/null 2>&1; then
  echo "error: stage4 binary failed source-check smoke (MCP/LSP would not start)" >&2
  exit 1
fi

if ! simple_binary_is_valid "${full_bin}"; then
  echo "error: stage4 binary failed the current frontend candidate gate" >&2
  exit 1
fi

run_logged stage4-redeploy-gate run_timeout_kill 180 sh \
  scripts/check/cert/redeploy_gate/redeploy_gate.shs "${full_bin}"

run_logged stage4-essential-tools-smoke run_timeout_kill 180 env \
  SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
  sh scripts/check/check-bootstrap-essential-tools-smoke.shs

stage4_provenance="${full_bin}.provenance.env"
stage4_write_candidate_provenance \
  "${full_bin}" "${stage4_provenance}" "${repo_root}" \
  "${bootstrap_script_path}" "${stage4_parent}" \
  "$(absolute_path "${stage3_provenance_manifest}")" \
  "${stage4_source_revision_before}" "${bootstrap_script_sha256_before}" \
  "${stage4_provenance_helper_sha256_before}" \
  "$(absolute_path "${bootstrap_lock}")" \
  "$(absolute_path "${log_dir}/stage4-native-build.log")" \
  "$(absolute_path "${log_dir}/stage4-essential-tools-smoke.log")" || {
    echo "error: refusing Stage 4 without canonical candidate provenance" >&2
    exit 1
  }
stage4_verify_candidate_provenance \
  "${stage4_provenance}" "${full_bin}" "${repo_root}" || {
    echo "error: Stage 4 candidate provenance did not re-verify" >&2
    exit 1
  }
echo "  Stage 4 provenance: ${stage4_provenance}"

echo "Stage 4b: compiling cached UI backend..."
bootstrap_progress_mark stage4b "$(absolute_path "${log_dir}/stage4b-ui-backend.log")"
ui_backend_bin="${full_dir}/simple_ui_backend${exe_suffix}"
prepare_native_cache stage4b-ui-backend
run_logged stage4b-ui-backend env RUST_LOG="${RUST_LOG:-error}" \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_STUB_MISSING_RT=1 \
  SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
  "${full_bin}" native-build \
    --backend "${backend}" \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads "${jobs}" --cache-dir "${native_cache_dir}" \
  --mode "${bootstrap_mode}" --entry src/app/ui/main.spl \
  --runtime-path "${stage_runtime_absolute}" \
  -o "${ui_backend_bin}"
[ -x "${ui_backend_bin}" ] || { echo "error: failed to compile cached UI backend" >&2; exit 1; }
echo "Full CLI binary: ${full_bin}"

# ===========================================================================
# Stage 5: Compile MCP servers (optional, skip with --no-mcp)
# ===========================================================================

mcp_build_ok=1
if [ "${build_mcp}" -eq 1 ]; then
  echo "Stage 5: compiling MCP servers..."
  bootstrap_progress_mark stage5 "$(absolute_path "${log_dir}/stage51-mcp-native-build.log")"

  # Build both servers before failing so both logs are available. The shared
  # fresh-artifact smoke below is the single fail-closed Stage 5 gate.
  mcp_stage=0
  for mcp_entry in "simple_mcp_server:src/app/mcp/main.spl" \
                    "simple_lsp_mcp_server:src/app/simple_lsp_mcp/main.spl"; do
    mcp_stage=$((mcp_stage + 1))
    mcp_name="${mcp_entry%%:*}"
    mcp_spl="${mcp_entry#*:}"
    mcp_log="stage5${mcp_stage}-mcp-native-build"

    echo "  Stage 5${mcp_stage}: ${mcp_name}"
    prepare_native_cache "stage5${mcp_stage}"
    rm -f "${full_dir}/${mcp_name}${exe_suffix}"
    set +e
    env RUST_LOG="${RUST_LOG:-error}" \
      SIMPLE_NO_DEPRECATED_WARNINGS=1 \
      LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
      SIMPLE_NO_STUB_FALLBACK=1 \
      SIMPLE_BUILD_PROGRESS_EVENTS="${build_progress_events}" \
      SIMPLE_BINARY="$(absolute_path "${stage_for_build}")" \
      "${stage_for_build}" native-build \
      --backend "${backend}" \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure \
      --threads "${jobs}" \
      --cache-dir "${native_cache_dir}" \
      --mode "${bootstrap_mode}" \
      --entry "${mcp_spl}" \
      --runtime-path "${stage_runtime_absolute}" \
      -o "${full_dir}/${mcp_name}${exe_suffix}" \
      >"${log_dir}/${mcp_log}.log" 2>&1
    mcp_status=$?
    set -e
    echo "  ${mcp_log} log: ${log_dir}/${mcp_log}.log"
    if [ "${mcp_status}" -ne 0 ]; then
      mcp_build_ok=0
      echo "  WARNING: ${mcp_name} build failed (exit ${mcp_status})"
    elif [ ! -s "${full_dir}/${mcp_name}${exe_suffix}" ]; then
      mcp_build_ok=0
      echo "  WARNING: ${mcp_name} produced a zero-byte file"
    else
      printf '%s\n' "$(hash_file "${full_dir}/${mcp_name}${exe_suffix}")" \
        >"${full_dir}/${mcp_name}${exe_suffix}.sha256"
      echo "  ${mcp_name}: ${full_dir}/${mcp_name}${exe_suffix}"
    fi
  done

  if [ "${mcp_build_ok}" -ne 1 ]; then
    echo "error: Stage 5 MCP server build failed; refusing stale artifacts" >&2
    exit 1
  fi

  echo "Stage 5 smoke: fresh MCP initialize/list/call gate"
  if ! env \
    SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
    MCP_SERVER="$(absolute_path "${full_dir}/simple_mcp_server${exe_suffix}")" \
    LSP_MCP_SERVER="$(absolute_path "${full_dir}/simple_lsp_mcp_server${exe_suffix}")" \
    MCP_NATIVE_BOOTSTRAP_FRESH=1 \
    sh scripts/check/check-mcp-native-smoke.shs; then
    echo "error: fresh Stage 5 MCP server smoke failed" >&2
    exit 1
  fi
else
  echo "Skipping MCP server builds (--no-mcp)"
fi

# ===========================================================================
# Deploy
# ===========================================================================

resume_stage4_verify_immutable || exit 1
if [ "${deploy}" -eq 1 ]; then
  bootstrap_progress_mark deploy ""
  deploy_dir="bin/release/${PLATFORM}"
  if [ -L "bin" ] || [ -L "bin/release" ]; then
    echo "ERROR: deploy refused - symlinked deployment parent" >&2
    exit 1
  fi
  mkdir -p "${deploy_dir}"
  if [ -L "${deploy_dir}" ]; then
    echo "ERROR: deploy refused - symlinked deployment directory: ${deploy_dir}" >&2
    exit 1
  fi
  deploy_lock_root="${deploy_dir}/.bootstrap-deploy-locks"
  if ! portable_lock_acquire "${deploy_lock_root}" deployment \
    "${SIMPLE_BOOTSTRAP_LOCK_WAIT_SECONDS:-30}"; then
    echo "ERROR: deploy refused - deployment is locked: ${deploy_dir}" >&2
    exit 1
  fi
  deploy_lock_handle=${PORTABLE_LOCK_HANDLE}

  # Deploy gate: never swap bin/simple to the self-hosted stage4 binary unless
  # a working seed driver exists at the delegate path. Without it the stage4
  # self-exec guard blocks `bin/simple test` host-wide (see
  # doc/08_tracking/bug/stage4_deploy_no_seed_test_runner_blocked_2026-06-11.md).
  seed_probe() {
    [ -x "$1" ] || return 1
    out="$(run_timeout 30 "$1" -c 'print(1+1)' 2>/dev/null)" || return 1
    [ "${out}" = "2" ]
  }
  if [ -z "${resume_stage4_output}" ]; then
    seed_delegate="${deploy_dir}/simple_seed${exe_suffix}"
    seed_src="${full_dir}/simple_seed${exe_suffix}"
    if ! seed_probe "${seed_src}"; then
      echo "ERROR: deploy refused — current seed driver failed smoke test: ${seed_src}." >&2
      exit 1
    fi
    install -m755 "${seed_src}" "${seed_delegate}"
    echo "Installed current seed delegate: ${seed_src} -> ${seed_delegate}"
  fi

  # Identity gate: bin/simple MUST be the pure-Simple self-hosted compiler and
  # never the Rust seed/driver (default tooling rule, .claude/rules/bootstrap.md).
  # Behavioural probes cannot tell them apart: the seed passes -c 'print(1+1)',
  # passes `test` 2-pass/1-fail, emits a .smf, and produces a running LLVM ELF.
  # Size and banner have BOTH failed as identity signals — a 154,185,152-byte
  # binary was the Rust driver while a 22,300,688-byte one was self-hosted.
  # The discriminator is a diagnostic string that only the pure-Simple compiler
  # sources carry into the emitted binary; it is absent from every Rust-driver
  # build (see src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl
  # and doc/08_tracking/bug/
  # bin_simple_bootstrap_main_stage_deployed_no_subcommands_2026-08-01.md).
  selfhost_identity_marker='enum construction: unregistered enum'
  selfhost_identity_ok() {
    [ -f "$1" ] || return 1
    if command -v strings >/dev/null 2>&1; then
      strings -a "$1" 2>/dev/null | grep -q "${selfhost_identity_marker}"
    else
      grep -a -q "${selfhost_identity_marker}" "$1" 2>/dev/null
    fi
  }
  if ! selfhost_identity_ok "${full_bin}"; then
    echo "ERROR: deploy refused — Stage 4 output is not the pure-Simple self-hosted compiler." >&2
    echo "  candidate: ${full_bin}" >&2
    echo "  identity probe found no self-hosted compiler marker (absent = Rust driver)." >&2
    echo "  Refusing to install a Rust seed/driver as ${deploy_dir}/simple${exe_suffix}." >&2
    exit 1
  fi
  echo "Identity gate: Stage 4 output verified pure-Simple self-hosted"

  deployed_bin="${deploy_dir}/simple${exe_suffix}"
  prev_bin="${deploy_dir}/simple${exe_suffix}.pre_deploy"
  deploy_receipt="${deploy_dir}/bootstrap-deploy-receipt.env"
  deploy_tmp="${deploy_dir}/.simple${exe_suffix}.deploy.$$"
  receipt_tmp="${deploy_dir}/.bootstrap-deploy-receipt.$$"
  rm -f "${deploy_receipt}"
  backup_created=0
  if [ -e "${deployed_bin}" ]; then
    if [ ! -f "${deployed_bin}" ] || [ -L "${deployed_bin}" ] || \
       ! selfhost_identity_ok "${deployed_bin}" || \
       [ "$(run_timeout 30 "${deployed_bin}" -c 'print(1+1)' 2>/dev/null)" != "2" ]; then
      echo "ERROR: deploy refused - current compiler is not a safe known-good backup." >&2
      exit 1
    fi
    prev_tmp="${deploy_dir}/.simple${exe_suffix}.pre_deploy.$$"
    install -m755 "${deployed_bin}" "${prev_tmp}"
    mv "${prev_tmp}" "${prev_bin}"
    backup_created=1
  else
    rm -f "${prev_bin}"
  fi
  install -m755 "${full_bin}" "${deploy_tmp}"
  mv "${deploy_tmp}" "${deployed_bin}"
  echo "Deployed full CLI binary to ${deployed_bin}"

  # Post-swap smoke: the deployed binary must evaluate code; restore on failure.
  if smoke_out="$(run_timeout 30 "${deployed_bin}" -c 'print(1+1)' 2>/dev/null)"; then
    :
  else
    smoke_out=""
  fi
  if [ "${smoke_out}" != "2" ]; then
    echo "ERROR: deployed binary failed smoke test (-c 'print(1+1)' -> '${smoke_out}')." >&2
    if [ "${backup_created}" -eq 1 ] && [ -x "${prev_bin}" ]; then
      restore_tmp="${deploy_dir}/.simple${exe_suffix}.restore.$$"
      install -m755 "${prev_bin}" "${restore_tmp}"
      mv "${restore_tmp}" "${deployed_bin}"
      echo "Restored previous binary to ${deployed_bin}" >&2
    else
      rm -f "${deployed_bin}"
    fi
    exit 1
  fi
  install -m755 "${ui_backend_bin}" "${deploy_dir}/simple_ui_backend${exe_suffix}"
  echo "Deployed cached UI backend to ${deploy_dir}/simple_ui_backend${exe_suffix}"

  # Deploy MCP servers if they were built successfully
  if [ "${build_mcp}" -eq 1 ] && [ "${mcp_build_ok}" -eq 1 ]; then
    for mcp_bin_name in simple_mcp_server simple_lsp_mcp_server; do
      if [ -x "${full_dir}/${mcp_bin_name}${exe_suffix}" ] && [ -s "${full_dir}/${mcp_bin_name}${exe_suffix}" ]; then
        mcp_deploy_tmp="${deploy_dir}/.${mcp_bin_name}${exe_suffix}.deploy.$$"
        mcp_hash_tmp="${deploy_dir}/.${mcp_bin_name}${exe_suffix}.sha256.deploy.$$"
        install -m755 "${full_dir}/${mcp_bin_name}${exe_suffix}" "${mcp_deploy_tmp}"
        install -m644 "${full_dir}/${mcp_bin_name}${exe_suffix}.sha256" "${mcp_hash_tmp}"
        mv "${mcp_deploy_tmp}" "${deploy_dir}/${mcp_bin_name}${exe_suffix}"
        mv "${mcp_hash_tmp}" "${deploy_dir}/${mcp_bin_name}${exe_suffix}.sha256"
        echo "Deployed ${mcp_bin_name} to ${deploy_dir}/${mcp_bin_name}${exe_suffix}"
      fi
    done
  fi

  # Recreate wrapper/launcher entrypoints (bin/simple plus release links)
  if [ "${os}" != "windows" ]; then
    if ! "${repo_root}/scripts/setup/setup.shs"; then
      echo "ERROR: deployment setup failed; restoring previous compiler" >&2
      if [ "${backup_created}" -eq 1 ] && [ -x "${prev_bin}" ]; then
        restore_tmp="${deploy_dir}/.simple${exe_suffix}.setup-restore.$$"
        install -m755 "${prev_bin}" "${restore_tmp}"
        mv "${restore_tmp}" "${deployed_bin}"
      else
        rm -f "${deployed_bin}"
      fi
      exit 1
    fi
  fi

  current_hash="$(hash_file "${deployed_bin}")"
  backup_hash="none"
  [ "${backup_created}" -eq 1 ] && [ -f "${prev_bin}" ] && [ ! -L "${prev_bin}" ] && backup_hash="$(hash_file "${prev_bin}")"
  {
    echo "schema=bootstrap-deploy-receipt-v1"
    echo "platform=${PLATFORM}"
    echo "current_path=${deployed_bin}"
    echo "current_sha256=${current_hash}"
    echo "backup_path=${prev_bin}"
    echo "backup_sha256=${backup_hash}"
    echo "timestamp_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "deployment_status=pass"
    echo "platform_acceptance_claimed=false"
  } > "${receipt_tmp}"
  chmod 644 "${receipt_tmp}"
  mv "${receipt_tmp}" "${deploy_receipt}"
  echo "Deployment receipt: ${deploy_receipt}"

  if [ "${release_tests}" -eq 1 ]; then
    echo "Stage 6: running release whole-test gate..."
    bootstrap_progress_mark stage6 ""
    run_logged stage6-whole-tests "${deployed_bin}" test test --whole --mode=interpreter
  fi
fi

resume_stage4_finalize || exit 1

echo "Final binary: ${full_bin}"

# ===========================================================================
# Exit status — reflect self-host verification result
# ===========================================================================

# Invariant net. A stage-3 failure sets stage4_is_seed=1, which refuses the seed
# fallback and exits 2 BEFORE Stage 4 and before any deploy, so reaching this
# point with stage3_ok=0 is a control-flow regression, not a known limitation.
# The message this block used to print ("Stage 4 used the Rust seed instead of
# the self-hosted compiler") described behaviour the script no longer has, and
# reading it as live was what led a lane to believe a failed self-host could
# still deploy. Keep the exit-2 contract, but report it as the invariant break
# it would be.
if [ "${stage3_ok:-0}" -eq 0 ]; then
  echo ""
  echo "ERROR: internal invariant broken — reached completion with stage3_ok=0." >&2
  echo "  A failed self-host must have exited at the seed-fallback refusal." >&2
  echo "  Treat any binary deployed by this run as unverified." >&2
  exit 2
fi
bootstrap_progress_mark complete ""
