#!/usr/bin/env bash
# ==============================================================================
# PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER
# Guarded by: scripts/check/fast-verify-bootstrap-scripts.shs
# ==============================================================================
set -euo pipefail

# Windows bootstrap entrypoint for Git Bash/MSYS2. Windows bootstrap uses
# Clang: target-qualified clang with llvm-ar for the MinGW UCRT default (gnu,
# repo-managed llvm-mingw) and clang-cl for the opt-in --msvc lane. Keep each
# lane bound to its C driver.

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
if [ "$#" -eq 0 ] && [ -t 0 ] && [ "${CI:-}" != "true" ] && [ "${SIMPLE_NONINTERACTIVE:-0}" != "1" ]; then
  cat >&2 <<'EOF_DEPRECATED'
DEPRECATED: Do not use scripts/bootstrap/bootstrap-windows.sh interactively without arguments for Phase 3/4 builds.
Use 'scripts/bootstrap/build-phase3-phase4.sh' (or 'scripts/bootstrap/build-phase3-phase4.bat' on Windows; default --win-config=mingw):
  Default / phased shard build: sh scripts/bootstrap/build-phase3-phase4.sh --phase=p3 --compile-mode=shard
  File-based parallel build:    sh scripts/bootstrap/build-phase3-phase4.sh --phase=p3 --compile-mode=file
  Phase 4 (release + xray):     sh scripts/bootstrap/build-phase3-phase4.sh --phase=p4
  Windows (mingw default):      scripts\bootstrap\build-phase3-phase4.bat --win-config=mingw --phase=p3
EOF_DEPRECATED
  printf 'Press Enter to return...' >&2
  if read -r _; then :; fi
  return 0 2>/dev/null || exit 0
fi
. "${script_dir}/bootstrap-windows-cl-mode.shs"
bootstrap_windows_preserve_cl_mode
abi="${SIMPLE_WINDOWS_ABI:-gnu}"
win_path_check=0
win_cfg_override=""
win_cmode="${SIMPLE_P3_COMPILE_MODE:-shard}"
win_cpu="x86_64"
if raw_win_arch=$(uname -m 2>/dev/null); then :; else raw_win_arch="x86_64"; fi
case "${raw_win_arch}" in
  arm64|aarch64|ARM64) win_cpu="aarch64" ;;
esac
forward=()

for arg in "$@"; do
  case "$arg" in
    --msvc) abi="msvc" ;;
    --mingw) abi="gnu" ;;
    --win-config=msvc) abi="msvc"; win_cfg_override="msvc" ;;
    --win-config=mingw|--win-config=gnu) abi="gnu"; win_cfg_override="mingw" ;;
    --win-config=*)
      echo "error: invalid --win-config='${arg#*=}' (expected mingw or msvc)" >&2
      exit 2
      ;;
    --path-check) win_path_check=1; forward+=("$arg") ;;
    --compile-mode=*|--p3-compile-mode=*) win_cmode="${arg#*=}"; forward+=("$arg") ;;
    --simulate-host=*)
      sim_val="${arg#*=}"
      case "${sim_val##*-}" in
        arm64|aarch64|ARM64) win_cpu="aarch64" ;;
        x86_64|amd64|AMD64) win_cpu="x86_64" ;;
      esac
      forward+=("$arg")
      ;;
    *) forward+=("$arg") ;;
  esac
done

# Help is read-only and exposes the canonical cache-policy flags before any
# submodule/materialization setup changes the checkout.
for arg in "${forward[@]}"; do
  case "$arg" in --help|-h) exec sh "${script_dir}/bootstrap-from-scratch.sh" "${forward[@]}" ;; esac
done

case "${abi}" in
  "") ;;
  gnu|msvc) export SIMPLE_WINDOWS_ABI="${abi}" ;;
  *) echo "error: SIMPLE_WINDOWS_ABI must be gnu or msvc" >&2; exit 1 ;;
esac

if [ "${win_path_check}" -eq 1 ]; then
  resolved_win_cfg="mingw"
  if [ "${abi}" = "msvc" ] || [ "${win_cfg_override}" = "msvc" ]; then
    resolved_win_cfg="msvc"
  fi
  printf 'PATH_ACTION|script=bootstrap-windows.sh|platform=windows|cpu=%s|win_config=%s|phase=init|step=windows-toolchain-select|compile_mode=%s|link_mode=dynlib|xray=0|release=0|status=ALIVE\n' \
    "${win_cpu}" "${resolved_win_cfg}" "${win_cmode}"
  win_sub_out=$(sh "${script_dir}/build-phase3-phase4.sh" --path-check --win-config="${resolved_win_cfg}" --compile-mode="${win_cmode}" --simulate-host="windows-${win_cpu}")
  printf '%s\n' "${win_sub_out}"
  win_sub_cnt=$(printf '%s\n' "${win_sub_out}" | awk '/^PATH_ACTION\|/ { n++ } END { print n + 0 }')
  win_total_cnt=$((win_sub_cnt + 1))
  win_target="${win_cpu}-pc-windows-gnu"
  if [ "${resolved_win_cfg}" = "msvc" ]; then
    win_target="${win_cpu}-pc-windows-msvc"
  fi
  printf 'PATH_SUMMARY|script=bootstrap-windows.sh|platform=windows|cpu=%s|win_config=%s|target=%s|actions=%s|status=PASS\n' \
    "${win_cpu}" "${resolved_win_cfg}" "${win_target}" "${win_total_cnt}"
  exit 0
fi

# Populate the recorded SPipe gitlink before materializing symlinks.  Several
# tracked documentation links resolve inside it, so the strict materializer
# must see the checked-out target rather than classify it as an unexpected
# pending link.  `git submodule update` uses the superproject's recorded
# commit; it does not follow a remote branch and leaves a dirty initialized
# checkout alone when Git refuses an unsafe update.
#
# .spipe/spipe is only a submodule at commits that record it as a gitlink
# (mode 160000); at later commits it is gone and `git submodule update` dies
# with "pathspec did not match", so skip when it is not registered.
spipe_gitlink=0
case "$(git -C "${repo_root}" ls-files -s -- .spipe/spipe 2>/dev/null)" in
  160000*) spipe_gitlink=1 ;;
esac
if [ "${spipe_gitlink}" = 1 ]; then
  git -C "${repo_root}" submodule update --init -- .spipe/spipe || {
    echo "error: cannot initialize recorded .spipe/spipe gitlink" >&2
    exit 1
  }
else
  echo "note: .spipe/spipe is not a registered submodule at this commit; skipping gitlink init"
fi
# Settle the fresh gitlink's index. A just-cloned checkout has unsettled stat
# data, so the Stage 3 consumer's hermetic `git status` (GIT_CONFIG_NOSYSTEM=1
# hides Git for Windows' system core.autocrlf=true; GIT_OPTIONAL_LOCKS=0 never
# writes a refreshed index) compares content, sees every CRLF file as
# modified (334 entries), and fails preflight with "git.gitlink-dirty". One
# ordinary status refreshes the stat cache; real content changes still report.
# The sleep clears Git's racy-clean window: a status in the checkout's own
# second leaves the entries unverified (measured: 289 dirty without it, 0 with).
if [ "${spipe_gitlink}" = 1 ]; then
  sleep 2
  git -C "${repo_root}/.spipe/spipe" status --porcelain >/dev/null 2>&1 || true
fi

# Preparation and receipt validation belong to the canonical startup owner.
# Preserve any caller-supplied receipt so stale authority fails closed there.

exec sh "${script_dir}/bootstrap-from-scratch.sh" "${forward[@]}"
