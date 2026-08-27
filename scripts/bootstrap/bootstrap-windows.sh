#!/usr/bin/env bash
set -euo pipefail

# Windows bootstrap entrypoint for Git Bash/MSYS2. The shared POSIX wrapper
# owns the pipeline so Windows follows the same pure-Simple/full-build policy.

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
abi="${SIMPLE_WINDOWS_ABI:-}"
forward=()

for arg in "$@"; do
  case "$arg" in
    --msvc) abi="msvc" ;;
    --mingw) abi="gnu" ;;
    *) forward+=("$arg") ;;
  esac
done

case "${abi}" in
  "") ;;
  gnu|msvc) export SIMPLE_WINDOWS_ABI="${abi}" ;;
  *) echo "error: SIMPLE_WINDOWS_ABI must be gnu or msvc" >&2; exit 1 ;;
esac

# Materialize git symlinks as NTFS junctions/hardlinks before anything else
# reads the tree. A checkout done by a Windows session that lacks a
# fresh-logon SeCreateSymbolicLinkPrivilege token (see
# doc/08_tracking/bug/windows_build_subcommand_silent_noop_stale_binary_2026-08-05.md)
# degrades every git symlink to a plain text placeholder file containing the
# literal target string — `src/compiler/backend` (an alias for the numbered
# `70.backend` layer dir) and dozens like it would silently resolve to
# nothing, breaking the loader in confusing ways far from this root cause.
# No-op, fast, and idempotent on a checkout where symlinks already resolved
# correctly (e.g. an elevated or Developer-Mode-since-logon session).
sh "${script_dir}/../setup/materialize-symlinks-windows.shs" "${script_dir}/../.." || {
  echo "warning: symlink materialization reported failures; continuing, but the build may hit missing-source errors below" >&2
}

exec sh "${script_dir}/bootstrap-from-scratch.sh" "${forward[@]}"
