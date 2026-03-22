#!/bin/sh
set -eu

# Simple Language — Post-clone / post-bootstrap setup
#
# Creates bin/simple → bin/release/<triple>/simple(.exe) symlink
# and sets up the development environment.
#
# Usage:
#   scripts/setup.sh [options]
#
# Options:
#   --prefix=<dir>   Install prefix for system-wide install (default: repo-local)
#   --triple=<T>     Override auto-detected platform triple
#   --dry-run        Show what would be done without doing it
#   --help           Show this help

usage() {
  cat <<'EOF'
Usage: scripts/setup.sh [options]

Post-clone / post-bootstrap setup for Simple Language.

Creates:
  bin/simple → bin/release/<arch>-<vendor>-<os>-<abi>/simple(.exe)

Options:
  --prefix=<dir>   Install prefix for symlink (default: repo bin/)
  --triple=<T>     Override auto-detected platform triple
  --dry-run        Show what would be done without doing it
  --help           Show this help

Examples:
  scripts/setup.sh                         # Auto-detect, create symlink
  scripts/setup.sh --triple=x86_64-pc-windows-gnu
  scripts/setup.sh --dry-run               # Preview only
EOF
}

prefix=""
triple_override=""
dry_run=0

while [ "$#" -gt 0 ]; do
  case "$1" in
    --prefix=*)   prefix="${1#*=}" ;;
    --triple=*)   triple_override="${1#*=}" ;;
    --dry-run)    dry_run=1 ;;
    --help|-h)    usage; exit 0 ;;
    *)            echo "error: unknown option '$1'" >&2; usage >&2; exit 1 ;;
  esac
  shift
done

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "${script_dir}/.." && pwd)

# ===========================================================================
# Platform detection — <arch>-<vendor>-<os>-<abi>
# ===========================================================================

detect_triple() {
  # Architecture
  local arch
  case "$(uname -m 2>/dev/null || echo unknown)" in
    x86_64|amd64)  arch="x86_64" ;;
    aarch64|arm64) arch="aarch64" ;;
    i686|i386)     arch="i686" ;;
    riscv64)       arch="riscv64" ;;
    *)             arch="x86_64" ;;
  esac

  # On Windows (MSYS2/Git Bash), uname -m may lie; prefer PROCESSOR_ARCHITECTURE
  if [ -n "${PROCESSOR_ARCHITECTURE:-}" ]; then
    case "${PROCESSOR_ARCHITECTURE}" in
      AMD64|x64)   arch="x86_64" ;;
      ARM64)       arch="aarch64" ;;
      x86)         arch="i686" ;;
    esac
  fi

  # OS, vendor, ABI
  local vendor="unknown"
  local os abi
  local host_os
  host_os=$(uname -s 2>/dev/null || echo unknown)

  case "${host_os}" in
    Linux)
      os="linux"; abi="gnu"
      ;;
    Darwin)
      os="darwin"; vendor="apple"; abi="macho"
      ;;
    FreeBSD)
      os="freebsd"; abi="elf"
      ;;
    MINGW*|MSYS*|CYGWIN*|Windows_NT)
      os="windows"; vendor="pc"
      # Detect MSVC vs MinGW
      if [ "${MSYSTEM:-}" != "${MSYSTEM#MINGW}" ] 2>/dev/null; then
        abi="gnu"
      elif command -v cl.exe >/dev/null 2>&1; then
        abi="msvc"
      elif command -v clang-cl >/dev/null 2>&1; then
        abi="msvc"
      elif command -v gcc >/dev/null 2>&1; then
        abi="gnu"
      else
        abi="msvc"
      fi
      ;;
    *)
      os=$(echo "${host_os}" | tr '[:upper:]' '[:lower:]')
      abi="elf"
      ;;
  esac

  echo "${arch}-${vendor}-${os}-${abi}"
}

if [ -n "${triple_override}" ]; then
  PLATFORM="${triple_override}"
else
  PLATFORM="$(detect_triple)"
fi

echo "Platform: ${PLATFORM}"

# Parse triple components
arch=$(echo "${PLATFORM}" | cut -d- -f1)
os=$(echo "${PLATFORM}" | cut -d- -f3)

# Executable extension
exe=""
if [ "${os}" = "windows" ]; then
  exe=".exe"
fi

# ===========================================================================
# Locate release binary
# ===========================================================================

release_dir="${repo_root}/bin/release"

# Try new triple-based path first, then legacy <os>-<arch> path, then flat
if [ -x "${release_dir}/${PLATFORM}/simple${exe}" ]; then
  release_bin="${PLATFORM}/simple${exe}"
elif [ -x "${release_dir}/${os}-${arch}/simple${exe}" ]; then
  # Legacy 2-part naming (linux-x86_64, windows-x86_64, etc.)
  release_bin="${os}-${arch}/simple${exe}"
elif [ -x "${release_dir}/simple${exe}" ]; then
  release_bin="simple${exe}"
else
  echo "error: no release binary found for ${PLATFORM}" >&2
  echo "" >&2
  echo "Searched:" >&2
  echo "  ${release_dir}/${PLATFORM}/simple${exe}" >&2
  echo "  ${release_dir}/${os}-${arch}/simple${exe}" >&2
  echo "  ${release_dir}/simple${exe}" >&2
  echo "" >&2
  echo "Run the bootstrap first:" >&2
  if [ "${os}" = "windows" ]; then
    echo "  scripts/bootstrap/bootstrap-windows.sh --deploy" >&2
  else
    echo "  scripts/bootstrap/bootstrap-from-scratch.sh --deploy" >&2
  fi
  exit 1
fi

echo "Release binary: bin/release/${release_bin}"

# ===========================================================================
# Create symlink
# ===========================================================================

bin_dir="${repo_root}/bin"
if [ -n "${prefix}" ]; then
  bin_dir="${prefix}/bin"
  mkdir -p "${bin_dir}"
fi

link_target="release/${release_bin}"
link_path="${bin_dir}/simple${exe}"

if [ "${dry_run}" -eq 1 ]; then
  echo ""
  echo "[dry-run] would create:"
  echo "  ${link_path} → ${link_target}"
  exit 0
fi

# Remove existing link or file (but not if it's a directory)
if [ -L "${link_path}" ] || [ -f "${link_path}" ]; then
  rm -f "${link_path}"
fi

# Create symlink (relative so the repo is relocatable)
cd "${bin_dir}"
ln -sf "${link_target}" "simple${exe}"

echo ""
echo "Created: bin/simple${exe} → ${link_target}"

# ===========================================================================
# Verify
# ===========================================================================

if [ -x "${link_path}" ] || [ "${os}" = "windows" ]; then
  echo ""
  echo "Verify:"
  echo "  bin/simple${exe} --version"
else
  echo ""
  echo "warning: binary is not executable, run: chmod +x ${release_dir}/${release_bin}" >&2
fi

echo ""
echo "Setup complete."
