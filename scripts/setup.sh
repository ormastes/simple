#!/bin/sh
set -eu

# Simple Language — Post-clone / post-bootstrap setup
#
# Creates symlink-only runtime entry points under bin/ and bin/release/
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

Creates symlink-only runtime entry points:
  bin/simple
  bin/release/simple
  bin/release/<arch>-<vendor>-<os>-<abi>/simple(.exe)

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

if [ -n "${triple_override}" ]; then
  FORCE_TRIPLE="${triple_override}"
fi
. "${repo_root}/scripts/platform-detect.sh"
PLATFORM="${PLATFORM_TRIPLE}"
arch="${PLATFORM_ARCH}"
os="${PLATFORM_OS}"
exe="${PLATFORM_EXE}"

echo "Platform: ${PLATFORM}"

# ===========================================================================
# Locate release binary
# ===========================================================================

release_dir="${repo_root}/bin/release"

# Locate release binary — only <triple>/simple(.exe) layout
if [ "${os}" = "windows" ]; then
  msvc_triple="${arch}-pc-windows-msvc"
  mingw_triple="${arch}-pc-windows-gnu"
  msvc_bin=""
  mingw_bin=""

  if [ -f "${release_dir}/${msvc_triple}/simple.exe" ]; then
    msvc_bin="${msvc_triple}/simple.exe"
  fi
  if [ -f "${release_dir}/${mingw_triple}/simple.exe" ]; then
    mingw_bin="${mingw_triple}/simple.exe"
  fi

  if [ -z "${msvc_bin}" ] && [ -z "${mingw_bin}" ]; then
    echo "error: no release binary found for Windows" >&2
    echo "  Expected: ${release_dir}/${msvc_triple}/simple.exe" >&2
    echo "       or:  ${release_dir}/${mingw_triple}/simple.exe" >&2
    echo "" >&2
    echo "Run the bootstrap first:" >&2
    echo "  scripts/bootstrap/bootstrap-windows.sh --deploy" >&2
    exit 1
  fi

  [ -n "${msvc_bin}" ]  && echo "MSVC binary:  bin/release/${msvc_bin}"
  [ -n "${mingw_bin}" ] && echo "MinGW binary: bin/release/${mingw_bin}"
else
  release_bin=""
  if [ -f "${release_dir}/${PLATFORM}/simple" ]; then
    release_bin="${PLATFORM}/simple"
  fi

  if [ -z "${release_bin}" ]; then
    echo "error: no release binary found for ${PLATFORM}" >&2
    echo "  Expected: ${release_dir}/${PLATFORM}/simple" >&2
    echo "" >&2
    echo "Run the bootstrap first:" >&2
    echo "  scripts/bootstrap/bootstrap-from-scratch.sh --deploy" >&2
    exit 1
  fi

  echo "Release binary: bin/release/${release_bin}"
fi

# Prefer the live Rust build outputs when they exist. Those binaries are rebuilt
# alongside the current source tree, while bin/release/<triple>/simple can be a
# stale deployed artifact.
preferred_runtime=""
if [ "${os}" != "windows" ]; then
  if [ -x "${repo_root}/src/compiler_rust/target/release/simple" ]; then
    preferred_runtime="${repo_root}/src/compiler_rust/target/release/simple"
  elif [ -x "${repo_root}/src/compiler_rust/target/bootstrap/simple" ]; then
    preferred_runtime="${repo_root}/src/compiler_rust/target/bootstrap/simple"
  fi
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

create_release_link() {
  local target="$1" link_path="$2"
  if [ -L "${link_path}" ] || [ -f "${link_path}" ]; then
    rm -f "${link_path}"
  fi
  mkdir -p "$(dirname "${link_path}")"
  ln -sf "${target}" "${link_path}"
  echo "  ${link_path#${repo_root}/} → ${target}"
}

if [ "${dry_run}" -eq 1 ]; then
  echo ""
  echo "[dry-run] would create:"
  if [ "${os}" = "windows" ]; then
    [ -n "${mingw_bin}" ] && echo "  bin/simple → release/${mingw_bin}"
    [ -n "${msvc_bin}" ]  && echo "  bin/simple.exe → release/${msvc_bin}"
  else
    if [ -n "${preferred_runtime}" ]; then
      echo "  bin/simple → ${preferred_runtime}"
      echo "  bin/release/simple → ${preferred_runtime}"
      echo "  bin/release/${PLATFORM}/simple → ${preferred_runtime}"
      echo "  bin/release/${os}-${arch}/simple → ${preferred_runtime}"
    else
      echo "  bin/simple → release/${release_bin}"
      echo "  bin/release/simple → ${release_bin}"
    fi
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
  if [ -n "${preferred_runtime}" ]; then
    create_link "${preferred_runtime}" "simple"
    create_release_link "${preferred_runtime}" "${release_dir}/${PLATFORM}/simple"
    create_release_link "${preferred_runtime}" "${release_dir}/${os}-${arch}/simple"
  else
    create_link "release/${release_bin}" "simple"
  fi
fi

# Clean up any stale bin/release/simple(.exe) flat file/symlink
for _stale in "${release_dir}/simple" "${release_dir}/simple.exe"; do
  [ -L "${_stale}" ] || [ -f "${_stale}" ] && rm -f "${_stale}" 2>/dev/null || true
done

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
# Resolve through symlinks to find the real script location
SELF="\$0"
while [ -L "\$SELF" ]; do
  DIR="\$(cd "\$(dirname "\$SELF")" && pwd)"
  SELF="\$(readlink "\$SELF")"
  case "\$SELF" in /*) ;; *) SELF="\${DIR}/\${SELF}" ;; esac
done
SCRIPT_DIR="\$(cd "\$(dirname "\$SELF")" && pwd)"
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
SELF="$0"
while [ -L "$SELF" ]; do
  DIR="$(cd "$(dirname "$SELF")" && pwd)"
  SELF="$(readlink "$SELF")"
  case "$SELF" in /*) ;; *) SELF="${DIR}/${SELF}" ;; esac
done
SCRIPT_DIR="$(cd "$(dirname "$SELF")" && pwd)"
REPO_ROOT="${SCRIPT_DIR}/../.."
RUNTIME="${SIMPLE_RUNTIME:-${SCRIPT_DIR}/../simple}"
if [ ! -x "$RUNTIME" ]; then RUNTIME="${SCRIPT_DIR}/simple"; fi
ENTRY="${REPO_ROOT}/examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl"
TRACE32_ROOT="${REPO_ROOT}/examples/10_tooling/trace32_tools"
DAEMON_DIR="/tmp/t32_lsp_mcp_shared"
cd "$REPO_ROOT"
export SIMPLE_LIB="${SIMPLE_LIB:-$TRACE32_ROOT}"
export SIMPLE_RUNTIME="${SIMPLE_RUNTIME:-$RUNTIME}"
export T32_LSP_MCP_TOOL_RUNNER="${T32_LSP_MCP_TOOL_RUNNER:-examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl}"
export T32_LSP_MCP_TOOL_DAEMON="${T32_LSP_MCP_TOOL_DAEMON:-examples/10_tooling/trace32_tools/cmm_lsp/mcp_daemon.spl}"
export T32_LSP_MCP_TOOL_DAEMON_DIR="${T32_LSP_MCP_TOOL_DAEMON_DIR:-$DAEMON_DIR}"
export SIMPLE_LOG="${SIMPLE_LOG:-error}"
if [ ! -f "$DAEMON_DIR/ready" ] && ! pgrep -f "tool_daemon.spl $DAEMON_DIR" >/dev/null 2>&1; then
  mkdir -p "$DAEMON_DIR"
  nohup "${SIMPLE_RUNTIME:-$RUNTIME}" "$T32_LSP_MCP_TOOL_DAEMON" "$DAEMON_DIR" >/dev/null 2>&1 </dev/null &
fi
RUST_LOG="${RUST_LOG:-error}" exec "${SIMPLE_RUNTIME:-$RUNTIME}" "$ENTRY" "$@"
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
