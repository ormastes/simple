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
      case "${MSYSTEM:-}" in
        MINGW*) abi="gnu" ;;
        *)
          if command -v cl.exe >/dev/null 2>&1; then
            abi="msvc"
          elif command -v clang-cl >/dev/null 2>&1; then
            abi="msvc"
          elif command -v gcc >/dev/null 2>&1; then
            abi="gnu"
          else
            abi="msvc"
          fi
          ;;
      esac
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

# Resolve a release binary: tries triple path, legacy path, flat path
# Usage: find_release_bin <platform> <os> <arch> <ext>
find_release_bin() {
  local plat="$1" fos="$2" farch="$3" fext="$4"
  if [ -f "${release_dir}/${plat}/simple${fext}" ]; then
    echo "${plat}/simple${fext}"; return 0
  elif [ -f "${release_dir}/${fos}-${farch}/simple${fext}" ]; then
    echo "${fos}-${farch}/simple${fext}"; return 0
  elif [ -f "${release_dir}/simple${fext}" ]; then
    echo "simple${fext}"; return 0
  fi
  return 1
}

# On Windows, create two links: bin/simple → MinGW, bin/simple.exe → MSVC
# On other platforms, create single link: bin/simple → release binary
if [ "${os}" = "windows" ]; then
  msvc_triple="${arch}-pc-windows-msvc"
  mingw_triple="${arch}-pc-windows-gnu"

  msvc_bin=""
  mingw_bin=""

  # Find MSVC binary
  if find_release_bin "${msvc_triple}" "${os}" "${arch}" ".exe" >/dev/null 2>&1; then
    msvc_bin="$(find_release_bin "${msvc_triple}" "${os}" "${arch}" ".exe")"
  fi

  # Find MinGW binary
  if find_release_bin "${mingw_triple}" "${os}" "${arch}" ".exe" >/dev/null 2>&1; then
    mingw_bin="$(find_release_bin "${mingw_triple}" "${os}" "${arch}" ".exe")"
  fi

  if [ -z "${msvc_bin}" ] && [ -z "${mingw_bin}" ]; then
    echo "error: no release binary found for Windows" >&2
    echo "" >&2
    echo "Searched:" >&2
    echo "  ${release_dir}/${msvc_triple}/simple.exe" >&2
    echo "  ${release_dir}/${mingw_triple}/simple.exe" >&2
    echo "  ${release_dir}/simple.exe" >&2
    echo "" >&2
    echo "Run the bootstrap first:" >&2
    echo "  scripts/bootstrap/bootstrap-windows.sh --msvc --deploy" >&2
    echo "  scripts/bootstrap/bootstrap-windows.sh --mingw --deploy" >&2
    exit 1
  fi

  if [ -n "${msvc_bin}" ]; then
    echo "MSVC binary:  bin/release/${msvc_bin}"
  else
    echo "warning: no MSVC binary found (${msvc_triple})" >&2
  fi
  if [ -n "${mingw_bin}" ]; then
    echo "MinGW binary: bin/release/${mingw_bin}"
  else
    echo "warning: no MinGW binary found (${mingw_triple})" >&2
  fi
else
  release_bin=""
  if find_release_bin "${PLATFORM}" "${os}" "${arch}" "" >/dev/null 2>&1; then
    release_bin="$(find_release_bin "${PLATFORM}" "${os}" "${arch}" "")"
  fi

  if [ -z "${release_bin}" ]; then
    echo "error: no release binary found for ${PLATFORM}" >&2
    echo "" >&2
    echo "Searched:" >&2
    echo "  ${release_dir}/${PLATFORM}/simple" >&2
    echo "  ${release_dir}/${os}-${arch}/simple" >&2
    echo "  ${release_dir}/simple" >&2
    echo "" >&2
    echo "Run the bootstrap first:" >&2
    echo "  scripts/bootstrap/bootstrap-from-scratch.sh --deploy" >&2
    exit 1
  fi

  echo "Release binary: bin/release/${release_bin}"
fi

# ===========================================================================
# Create symlinks
# ===========================================================================

bin_dir="${repo_root}/bin"
if [ -n "${prefix}" ]; then
  bin_dir="${prefix}/bin"
  mkdir -p "${bin_dir}"
fi

create_link() {
  local target="$1" name="$2"
  local lpath="${bin_dir}/${name}"
  if [ -L "${lpath}" ] || [ -f "${lpath}" ]; then
    rm -f "${lpath}"
  fi
  cd "${bin_dir}"
  ln -sf "${target}" "${name}"
  echo "  ${name} → ${target}"
}

if [ "${dry_run}" -eq 1 ]; then
  echo ""
  echo "[dry-run] would create:"
  if [ "${os}" = "windows" ]; then
    [ -n "${mingw_bin}" ] && echo "  bin/simple → release/${mingw_bin}"
    [ -n "${msvc_bin}" ]  && echo "  bin/simple.exe → release/${msvc_bin}"
  else
    echo "  bin/simple → release/${release_bin}"
  fi
  exit 0
fi

echo ""
echo "Creating links:"

if [ "${os}" = "windows" ]; then
  # bin/simple (no ext) → MinGW binary (for MSYS2 / Git Bash)
  if [ -n "${mingw_bin}" ]; then
    create_link "release/${mingw_bin}" "simple"
  fi
  # bin/simple.exe → MSVC binary (for CMD / PowerShell)
  if [ -n "${msvc_bin}" ]; then
    create_link "release/${msvc_bin}" "simple.exe"
  fi
else
  create_link "release/${release_bin}" "simple"
fi

# Also create bin/release/simple → <platform>/simple symlink
release_link_path="${release_dir}/simple${exe}"
release_link_target="${release_bin}"
if [ -L "${release_link_path}" ] || [ -f "${release_link_path}" ]; then
  rm -f "${release_link_path}"
fi
cd "${release_dir}"
ln -sf "${release_link_target}" "simple${exe}"

echo "Created: bin/release/simple${exe} → ${release_link_target}"

# ===========================================================================
# MCP launcher scripts in bin/release/ (targets for bin/*_mcp_server symlinks)
# ===========================================================================

generate_mcp_launcher() {
  local name="$1" entry="$2" extra_env="$3"
  local launcher="${release_dir}/${name}"
  cat > "${launcher}" <<LAUNCHER_EOF
#!/bin/sh
# Auto-generated by scripts/setup.sh — do not edit
set -eu
SCRIPT_DIR="\$(cd "\$(dirname "\$0")" && pwd)"
REPO_ROOT="\${SCRIPT_DIR}/../.."
# Prefer bin/simple (user-managed link) so all tools follow the same binary
RUNTIME="\${SCRIPT_DIR}/../simple"
if [ ! -x "\$RUNTIME" ]; then RUNTIME="\${SCRIPT_DIR}/simple"; fi
ENTRY="\${REPO_ROOT}/${entry}"
export SIMPLE_LIB="\${REPO_ROOT}/src"
export SIMPLE_LOG=error
${extra_env}
RUST_LOG=error exec "\$RUNTIME" "\$ENTRY" "\$@" 2>/dev/null
LAUNCHER_EOF
  chmod +x "${launcher}"
}

echo ""
echo "Generating MCP launcher scripts in bin/release/:"

generate_mcp_launcher "simple_mcp_server" \
  "src/app/mcp/main.spl" ""
echo "  simple_mcp_server"

generate_mcp_launcher "simple_lsp_mcp_server" \
  "src/app/simple_lsp_mcp/main.spl" \
  'export SIMPLE_BINARY="$RUNTIME"'
echo "  simple_lsp_mcp_server"

generate_mcp_launcher "t32_mcp_server" \
  "examples/10_tooling/trace32_tools/t32_mcp/main.spl" \
  'export SIMPLE_LIB="${REPO_ROOT}/examples/10_tooling/trace32_tools"
cd "$REPO_ROOT"'
echo "  t32_mcp_server"

cat > "${release_dir}/t32_lsp_mcp_server" <<'T32LSP_EOF'
#!/bin/sh
# Auto-generated by scripts/setup.sh — do not edit
set -eu
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="${SCRIPT_DIR}/../.."
RUNTIME="${SCRIPT_DIR}/../simple"
if [ ! -x "$RUNTIME" ]; then RUNTIME="${SCRIPT_DIR}/simple"; fi
ENTRY="${REPO_ROOT}/examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl"
TRACE32_ROOT="${REPO_ROOT}/examples/10_tooling/trace32_tools"
DAEMON_DIR="/tmp/t32_lsp_mcp_shared"
cd "$REPO_ROOT"
export SIMPLE_LIB="$TRACE32_ROOT"
export SIMPLE_RUNTIME="$RUNTIME"
export T32_LSP_MCP_TOOL_RUNNER="examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl"
export T32_LSP_MCP_TOOL_DAEMON="examples/10_tooling/trace32_tools/cmm_lsp/mcp_daemon.spl"
export T32_LSP_MCP_TOOL_DAEMON_DIR="$DAEMON_DIR"
export SIMPLE_LOG=error
if [ ! -f "$DAEMON_DIR/ready" ] && ! pgrep -f "tool_daemon.spl $DAEMON_DIR" >/dev/null 2>&1; then
  mkdir -p "$DAEMON_DIR"
  nohup "$RUNTIME" "$T32_LSP_MCP_TOOL_DAEMON" "$DAEMON_DIR" >/dev/null 2>&1 </dev/null &
fi
RUST_LOG=error exec "$RUNTIME" "$ENTRY" "$@" 2>/dev/null
T32LSP_EOF
chmod +x "${release_dir}/t32_lsp_mcp_server"
echo "  t32_lsp_mcp_server"

# Recreate bin/ symlinks to release/ (in case they're missing or stale)
for mcp_name in simple_mcp_server simple_lsp_mcp_server t32_mcp_server t32_lsp_mcp_server; do
  mcp_link="${bin_dir}/${mcp_name}"
  if [ -L "${mcp_link}" ] || [ -f "${mcp_link}" ]; then
    rm -f "${mcp_link}"
  fi
  cd "${bin_dir}"
  ln -sf "release/${mcp_name}" "${mcp_name}"
done
echo "  Linked bin/*_mcp_server → release/*"

# ===========================================================================
# Claude command symlinks (.claude/commands/ → .claude/skills/)
# ===========================================================================

skills_dir="${repo_root}/.claude/skills"
commands_dir="${repo_root}/.claude/commands"

if [ -d "${skills_dir}" ]; then
  mkdir -p "${commands_dir}"
  # Remove stale symlinks that no longer have a target skill
  for f in "${commands_dir}"/*.md; do
    [ -L "$f" ] && [ ! -e "$f" ] && rm -f "$f"
  done
  link_count=0
  for f in "${skills_dir}"/*.md; do
    [ -f "$f" ] || continue
    fname=$(basename "$f")
    rm -f "${commands_dir}/${fname}"
    cd "${commands_dir}"
    ln -sf "../skills/${fname}" "${fname}"
    link_count=$((link_count + 1))
  done
  echo ""
  echo "Created: ${link_count} command symlinks in .claude/commands/"
fi

# ===========================================================================
# Codex parity symlinks (.codex/commands/ → .codex/skills/*/SKILL.md)
# ===========================================================================

codex_skills_dir="${repo_root}/.codex/skills"
codex_commands_dir="${repo_root}/.codex/commands"

if [ -d "${codex_skills_dir}" ]; then
  mkdir -p "${codex_commands_dir}"
  # Remove stale symlinks
  for f in "${codex_commands_dir}"/*.md; do
    [ -L "$f" ] && [ ! -e "$f" ] && rm -f "$f"
  done
  link_count=0
  for f in "${codex_skills_dir}"/*/SKILL.md; do
    [ -f "$f" ] || continue
    skill_name=$(basename "$(dirname "$f")")
    rm -f "${codex_commands_dir}/${skill_name}.md"
    cd "${codex_commands_dir}"
    ln -sf "../skills/${skill_name}/SKILL.md" "${skill_name}.md"
    link_count=$((link_count + 1))
  done
  echo "Created: ${link_count} parity links in .codex/commands/"
fi

# ===========================================================================
# Verify
# ===========================================================================

echo ""
echo "Verify:"
if [ "${os}" = "windows" ]; then
  [ -n "${mingw_bin}" ] && echo "  bin/simple --version       (MinGW, for bash)"
  [ -n "${msvc_bin}" ]  && echo "  bin\\simple.exe --version   (MSVC, for CMD)"
else
  echo "  bin/simple --version"
fi

echo ""
echo "Setup complete."
