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

exec sh "${script_dir}/bootstrap-from-scratch.sh" "${forward[@]}"
