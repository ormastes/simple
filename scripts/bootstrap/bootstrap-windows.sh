#!/usr/bin/env bash
set -euo pipefail

# Windows bootstrap entrypoint for Git Bash/MSYS2. Windows bootstrap uses
# Clang: clang-cl for the MSVC default and target-qualified clang with llvm-ar
# for --mingw. Keep each lane bound to its C driver.

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
. "${script_dir}/bootstrap-windows-cl-mode.shs"
bootstrap_windows_preserve_cl_mode
abi="${SIMPLE_WINDOWS_ABI:-msvc}"
forward=()

for arg in "$@"; do
  case "$arg" in
    --msvc) abi="msvc" ;;
    --mingw) abi="gnu" ;;
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

# Populate the recorded SPipe gitlink before materializing symlinks.  Several
# tracked documentation links resolve inside it, so the strict materializer
# must see the checked-out target rather than classify it as an unexpected
# pending link.  `git submodule update` uses the superproject's recorded
# commit; it does not follow a remote branch and leaves a dirty initialized
# checkout alone when Git refuses an unsafe update.
git -C "${repo_root}" submodule update --init -- .spipe/spipe || {
  echo "error: cannot initialize recorded .spipe/spipe gitlink" >&2
  exit 1
}
# Settle the fresh gitlink's index. A just-cloned checkout has unsettled stat
# data, so the Stage 3 consumer's hermetic `git status` (GIT_CONFIG_NOSYSTEM=1
# hides Git for Windows' system core.autocrlf=true; GIT_OPTIONAL_LOCKS=0 never
# writes a refreshed index) compares content, sees every CRLF file as
# modified (334 entries), and fails preflight with "git.gitlink-dirty". One
# ordinary status refreshes the stat cache; real content changes still report.
# The sleep clears Git's racy-clean window: a status in the checkout's own
# second leaves the entries unverified (measured: 289 dirty without it, 0 with).
sleep 2
git -C "${repo_root}/.spipe/spipe" status --porcelain >/dev/null 2>&1 || true

# Preparation and receipt validation belong to the canonical startup owner.
# Preserve any caller-supplied receipt so stale authority fails closed there.

exec sh "${script_dir}/bootstrap-from-scratch.sh" "${forward[@]}"
