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
  bin/release/<platform>/simple
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
host_kernel=$(uname -s 2>/dev/null || echo unknown)
host_runtime_os="unknown"
case "${host_kernel}" in
  Linux) host_runtime_os="linux" ;;
  Darwin) host_runtime_os="darwin" ;;
  FreeBSD) host_runtime_os="freebsd" ;;
  MINGW*|MSYS*|CYGWIN*|Windows_NT) host_runtime_os="windows" ;;
esac

# Returns 0 if file is (or transitively resolves to) a Rust build artifact.
is_rust_artifact() {
  local target="$1"
  local resolved="$target"
  while [ -L "$resolved" ]; do
    local link
    link="$(readlink "$resolved")"
    case "$link" in
      /*) resolved="$link" ;;
      *)  resolved="$(dirname "$resolved")/$link" ;;
    esac
  done
  case "$resolved" in
    */src/compiler_rust/target/*) return 0 ;;
    *) return 1 ;;
  esac
}

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
if [ "${PLATFORM_WSL:-0}" = "1" ]; then
  echo "WSL:      detected (Windows Subsystem for Linux)"
fi

# ===========================================================================
# Locate preferred runtime / release binary
# ===========================================================================

release_dir="${repo_root}/bin/release"
mcp_release_subdir="${PLATFORM}"

# Prefer the self-hosted bootstrap binary when it exists (pure Simple, no Rust seed).
# Fall back to Rust build outputs only if no self-hosted binary is available.
preferred_runtime=""
if [ "${os}" != "windows" ]; then
  if [ "${os}" = "${host_runtime_os}" ] && [ -x "${repo_root}/build/bootstrap/stage2_full/simple" ]; then
    preferred_runtime="${repo_root}/build/bootstrap/stage2_full/simple"
  elif [ "${os}" = "${host_runtime_os}" ] && [ -x "${repo_root}/src/compiler_rust/target/release/simple" ]; then
    preferred_runtime="${repo_root}/src/compiler_rust/target/release/simple"
  elif [ "${os}" = "${host_runtime_os}" ] && [ -x "${repo_root}/src/compiler_rust/target/bootstrap/simple" ]; then
    preferred_runtime="${repo_root}/src/compiler_rust/target/bootstrap/simple"
  elif [ "${os}" = "freebsd" ] && [ -x "${repo_root}/bin/freebsd/simple" ]; then
    preferred_runtime="${repo_root}/bin/freebsd/simple"
  fi
fi

# Resolve a self-hosted release binary.
# Skips symlinks that resolve to Rust build artifacts (from previous fallback setups).
# Target-specific paths are always valid. The flat bin/release/simple fallback is
# only kept for legacy compatibility when the target runtime OS matches the host.
find_release_bin() {
  local plat="$1" fos="$2" farch="$3" fext="$4"
  if [ -f "${release_dir}/${plat}/simple${fext}" ] && ! is_rust_artifact "${release_dir}/${plat}/simple${fext}"; then
    echo "${plat}/simple${fext}"; return 0
  elif [ -f "${release_dir}/${fos}-${farch}/simple${fext}" ] && ! is_rust_artifact "${release_dir}/${fos}-${farch}/simple${fext}"; then
    echo "${fos}-${farch}/simple${fext}"; return 0
  elif [ "${fos}" = "${host_runtime_os}" ] && [ -f "${release_dir}/simple${fext}" ] && ! is_rust_artifact "${release_dir}/simple${fext}"; then
    echo "simple${fext}"; return 0
  fi
  return 1
}

if [ "${os}" = "windows" ]; then
  msvc_triple="${arch}-pc-windows-msvc"
  mingw_triple="${arch}-pc-windows-gnu"
  msvc_bin=""
  mingw_bin=""

  if find_release_bin "${msvc_triple}" "${os}" "${arch}" ".exe" >/dev/null 2>&1; then
    msvc_bin="$(find_release_bin "${msvc_triple}" "${os}" "${arch}" ".exe")"
  fi
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

  if [ -z "${release_bin}" ] && [ -z "${preferred_runtime}" ]; then
    echo "error: no release binary found for ${PLATFORM}" >&2
    echo "" >&2
    echo "Searched:" >&2
    echo "  ${release_dir}/${PLATFORM}/simple" >&2
    echo "  ${release_dir}/${os}-${arch}/simple" >&2
    echo "  ${release_dir}/simple" >&2
    if [ "${os}" = "freebsd" ]; then
      echo "  ${repo_root}/bin/freebsd/simple" >&2
    fi
    echo "" >&2
    echo "Run the bootstrap first:" >&2
    echo "  scripts/bootstrap/bootstrap-from-scratch.sh --deploy" >&2
    exit 1
  fi

  if [ -n "${release_bin}" ]; then
    echo "Release binary: bin/release/${release_bin}"
    case "${release_bin}" in
      */*) mcp_release_subdir="$(dirname "${release_bin}")" ;;
    esac
  else
    echo "Preferred runtime: ${preferred_runtime}"
  fi
fi

mcp_release_dir="${release_dir}/${mcp_release_subdir}"
mkdir -p "${mcp_release_dir}"

# ===========================================================================
# Create symlinks
# ===========================================================================

bin_dir="${repo_root}/bin"
if [ -n "${prefix}" ]; then
  bin_dir="${prefix}/bin"
  mkdir -p "${bin_dir}"
fi

# Atomic symlink creation: create a temp link then mv over the target.
# This avoids a window where the link doesn't exist (rm + ln race).
# Falls back to plain ln -sf on platforms where mv over symlinks fails.
# On Windows/MSYS2, sets MSYS=winsymlinks:nativestrict to create real
# NTFS symlinks instead of file copies (default MSYS2 behavior).
create_link() {
  local target="$1" name="$2"
  local lpath="${bin_dir}/${name}"
  local tmp="${lpath}.setup_tmp.$$"
  cd "${bin_dir}"
  # On MSYS2/Windows, default ln -s creates copies. Force native symlinks.
  local _ln_env=""
  case "${host_kernel}" in
    MINGW*|MSYS*|CYGWIN*) _ln_env="MSYS=winsymlinks:nativestrict" ;;
  esac
  env ${_ln_env} ln -sf "${target}" "${tmp}" 2>/dev/null && mv -f "${tmp}" "${lpath}" 2>/dev/null \
    || { rm -f "${tmp}" 2>/dev/null; rm -f "${lpath}"; env ${_ln_env} ln -sf "${target}" "${name}"; }
  # Validate: link should resolve to an executable
  if [ -L "${lpath}" ] && ! [ -e "${lpath}" ]; then
    echo "  [WARN] ${name} → ${target} (dangling — target does not exist yet)" >&2
  else
    echo "  ${name} → ${target}"
  fi
}

create_release_link() {
  local target="$1" link_path="$2"
  local tmp="${link_path}.setup_tmp.$$"
  mkdir -p "$(dirname "${link_path}")"
  local _ln_env=""
  case "${host_kernel}" in
    MINGW*|MSYS*|CYGWIN*) _ln_env="MSYS=winsymlinks:nativestrict" ;;
  esac
  env ${_ln_env} ln -sf "${target}" "${tmp}" 2>/dev/null && mv -f "${tmp}" "${link_path}" 2>/dev/null \
    || { rm -f "${tmp}" 2>/dev/null; rm -f "${link_path}"; env ${_ln_env} ln -sf "${target}" "${link_path}"; }
  if [ -L "${link_path}" ] && ! [ -e "${link_path}" ]; then
    echo "  [WARN] ${link_path#${repo_root}/} → ${target} (dangling)" >&2
  else
    echo "  ${link_path#${repo_root}/} → ${target}"
  fi
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
      echo "  bin/release/<platform>/simple → ${preferred_runtime}"
      echo "  bin/release/${PLATFORM}/simple → ${preferred_runtime}"
      echo "  bin/release/${os}-${arch}/simple → ${preferred_runtime}"
    else
      echo "  bin/simple → release/${release_bin}"
      echo "  bin/release/<platform>/simple → ${release_bin}"
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
  if [ -n "${release_bin}" ]; then
    # Self-hosted binary found — use it (preferred)
    create_link "release/${release_bin}" "simple"
  elif [ -n "${preferred_runtime}" ]; then
    # No self-hosted binary — fall back to Rust (temporary until bootstrap)
    echo "  (warning: using Rust fallback — run bootstrap to get self-hosted binary)"
    create_link "${preferred_runtime}" "simple"
    create_release_link "${preferred_runtime}" "${release_dir}/${PLATFORM}/simple"
    create_release_link "${preferred_runtime}" "${release_dir}/${os}-${arch}/simple"
  fi
fi

# Clean up Rust-pointing symlinks at bin/release/simple(.exe), but preserve real self-hosted binaries
for _stale in "${release_dir}/simple" "${release_dir}/simple.exe"; do
  if [ -L "${_stale}" ] && is_rust_artifact "${_stale}"; then
    rm -f "${_stale}" 2>/dev/null || true
    echo "  Removed stale Rust symlink: ${_stale#${repo_root}/}"
  fi
done

# ===========================================================================
# MCP launcher scripts in bin/release/ (targets for bin/*_mcp_server symlinks)
# ===========================================================================

generate_mcp_launcher() {
  local name="$1" entry="$2" extra_env="$3" preferred_binary="${4:-}"
  local launcher="${mcp_release_dir}/${name}"
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
REPO_ROOT=""
SEARCH_DIR="\$SCRIPT_DIR"
while [ "\$SEARCH_DIR" != "/" ]; do
  if [ -d "\${SEARCH_DIR}/src" ] && [ -d "\${SEARCH_DIR}/bin" ]; then
    REPO_ROOT="\$SEARCH_DIR"
    break
  fi
  SEARCH_DIR="\$(dirname "\$SEARCH_DIR")"
done
if [ -z "\$REPO_ROOT" ]; then
  echo "error: failed to locate repo root for ${name}" >&2
  exit 1
fi
cd "\$REPO_ROOT"
RUNTIME="\${REPO_ROOT}/src/compiler_rust/target/release/simple"
if [ ! -x "\$RUNTIME" ]; then RUNTIME="\${REPO_ROOT}/src/compiler_rust/target/bootstrap/simple"; fi
if [ ! -x "\$RUNTIME" ]; then RUNTIME="\${SCRIPT_DIR}/simple"; fi
if [ ! -x "\$RUNTIME" ]; then RUNTIME="\${REPO_ROOT}/bin/simple"; fi
if [ ! -x "\$RUNTIME" ]; then RUNTIME="\${REPO_ROOT}/bin/release/simple"; fi
if [ ! -x "\$RUNTIME" ]; then echo "error: no runtime found for ${name}" >&2; exit 1; fi
ENTRY="\${REPO_ROOT}/${entry}"
STDERR_LOG="\${REPO_ROOT}/.simple/logs/${name}_stderr.log"
mkdir -p "\$(dirname "\$STDERR_LOG")"
export SIMPLE_LIB="\${REPO_ROOT}/src"
export SIMPLE_LOG=error
export SIMPLE_BINARY="\$RUNTIME"
export SIMPLE_TIMEOUT_SECONDS=86400
export SIMPLE_MEMORY_LIMIT_MB=\${SIMPLE_MEMORY_LIMIT_MB:-\${SIMPLE_TEST_MEMORY_LIMIT_MB:-100}}
${extra_env}
RUST_LOG=error exec "\$RUNTIME" run "\$ENTRY" "\$@" 2>>"\$STDERR_LOG"
LAUNCHER_EOF
  chmod +x "${launcher}"
}

echo ""
echo "Generating MCP launcher scripts in ${mcp_release_dir#${repo_root}/}:"

generate_mcp_launcher "simple_mcp_server" \
  "src/app/mcp/main.spl" "" ""
echo "  simple_mcp_server"

generate_mcp_launcher "simple_lsp_mcp_server" \
  "src/app/simple_lsp_mcp/main.spl" \
  'export SIMPLE_BINARY="$RUNTIME"' ""
echo "  simple_lsp_mcp_server"

cat > "${mcp_release_dir}/t32_mcp_server" <<'T32_MCP_EOF'
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
REPO_ROOT=""
SEARCH_DIR="$SCRIPT_DIR"
while [ "$SEARCH_DIR" != "/" ]; do
  if [ -d "${SEARCH_DIR}/src" ] && [ -d "${SEARCH_DIR}/bin" ]; then
    REPO_ROOT="$SEARCH_DIR"
    break
  fi
  SEARCH_DIR="$(dirname "$SEARCH_DIR")"
done
if [ -z "$REPO_ROOT" ]; then
  echo "error: failed to locate repo root for t32_mcp" >&2
  exit 1
fi
RUNTIME="${SIMPLE_BINARY:-}"
if [ -n "$RUNTIME" ] && [ ! -x "$RUNTIME" ]; then
  RUNTIME=""
fi

t32_mcp_sanitize_segment() {
  printf '%s' "$1" | sed 's#^/*##; s#[^A-Za-z0-9._-]#_#g'
}

t32_mcp_debug_enabled() {
  case "${T32_MCP_DEBUG_LOG:-0}" in
    0|false|FALSE|no|NO|off|OFF) return 1 ;;
  esac
  return 0
}

t32_mcp_debug_root() {
  if [ -n "${T32_MCP_DEBUG_ROOT:-}" ]; then
    printf '%s' "$T32_MCP_DEBUG_ROOT"
    return 0
  fi
  t32_mcp_debug_cwd="$(pwd)"
  t32_mcp_debug_segment="$(t32_mcp_sanitize_segment "$t32_mcp_debug_cwd")"
  if [ -z "$t32_mcp_debug_segment" ]; then
    t32_mcp_debug_segment="workspace"
  fi
  printf '%s' "/tmp/t32_mcp_debug_${t32_mcp_debug_segment}"
}

t32_mcp_log_line() {
  t32_mcp_log_file="$1"
  shift
  printf '%s %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$*" >>"$t32_mcp_log_file"
}

t32_mcp_startup_log() {
  if [ "$DEBUG_ENABLED" != "1" ]; then
    return 0
  fi
  t32_mcp_log_line "${DEBUG_ROOT}/startup.log" "$@"
}

t32_mcp_native_health_cache_path() {
  t32_mcp_health_cwd="$(pwd)"
  t32_mcp_health_segment="$(t32_mcp_sanitize_segment "$t32_mcp_health_cwd")"
  if [ -z "$t32_mcp_health_segment" ]; then
    t32_mcp_health_segment="workspace"
  fi
  printf '%s' "/tmp/t32_mcp_native_health_${t32_mcp_health_segment}.state"
}

t32_mcp_native_signature() {
  t32_mcp_native_bin="$1"
  if stat -c '%Y:%s' "$t32_mcp_native_bin" >/dev/null 2>&1; then
    stat -c '%Y:%s' "$t32_mcp_native_bin"
  else
    stat -f '%m:%z' "$t32_mcp_native_bin"
  fi
}

t32_mcp_native_health_cached() {
  t32_mcp_cache_file="$1"
  t32_mcp_expected_sig="$2"
  if [ ! -f "$t32_mcp_cache_file" ]; then
    return 1
  fi
  t32_mcp_cached_sig="$(sed -n 's/^sig=//p' "$t32_mcp_cache_file" | head -n 1)"
  t32_mcp_cached_status="$(sed -n 's/^status=//p' "$t32_mcp_cache_file" | head -n 1)"
  if [ "$t32_mcp_cached_sig" = "$t32_mcp_expected_sig" ] && [ -n "$t32_mcp_cached_status" ]; then
    printf '%s' "$t32_mcp_cached_status"
    return 0
  fi
  return 1
}

t32_mcp_native_health_probe() {
  t32_mcp_native_bin="$1"
  "$t32_mcp_native_bin" --version >/dev/null 2>&1 &
  t32_mcp_probe_pid=$!
  (
    sleep 2
    kill "$t32_mcp_probe_pid" >/dev/null 2>&1 || true
  ) &
  t32_mcp_killer_pid=$!
  wait "$t32_mcp_probe_pid"
  t32_mcp_probe_status=$?
  kill "$t32_mcp_killer_pid" >/dev/null 2>&1 || true
  wait "$t32_mcp_killer_pid" >/dev/null 2>&1 || true
  return "$t32_mcp_probe_status"
}

DEBUG_ENABLED=0
DEBUG_ROOT=""
WRAPPER_LOG=""
FRONTEND_LOG=""
REQUESTS_LOG=""
WORKER_LOG=""
ERROR_LOG=""

if t32_mcp_debug_enabled; then
  DEBUG_ENABLED=1
  DEBUG_ROOT="$(t32_mcp_debug_root)"
  mkdir -p "$DEBUG_ROOT"
  WRAPPER_LOG="${DEBUG_ROOT}/wrapper.log"
  FRONTEND_LOG="${DEBUG_ROOT}/frontend.log"
  REQUESTS_LOG="${DEBUG_ROOT}/requests.log"
  WORKER_LOG="${DEBUG_ROOT}/worker.log"
  ERROR_LOG="${DEBUG_ROOT}/errors.log"
  : > "$WRAPPER_LOG"
  : > "$FRONTEND_LOG"
  : > "$REQUESTS_LOG"
  : > "$WORKER_LOG"
  : > "$ERROR_LOG"
fi

PREFERRED_BINARY=""
if [ -x "${REPO_ROOT}/bin/release/t32_mcp_native" ]; then
  PREFERRED_BINARY="${REPO_ROOT}/bin/release/t32_mcp_native"
fi
HOST_KERNEL="$(uname -s 2>/dev/null || echo unknown)"
NATIVE_REQUESTED=0
case "${T32_MCP_USE_NATIVE:-auto}" in
  0|false|FALSE|no|NO|off|OFF)
    NATIVE_REQUESTED=0
    ;;
  *)
    if [ -n "$PREFERRED_BINARY" ] || [ "$HOST_KERNEL" = "FreeBSD" ]; then
      NATIVE_REQUESTED=1
    fi
    ;;
esac

NATIVE_HEALTH_CACHE=""
NATIVE_HEALTH_STATUS="unknown"
RUNTIME_KIND=""
if [ -n "$RUNTIME" ]; then
  RUNTIME_KIND="env-simple-binary"
elif [ "$NATIVE_REQUESTED" = "1" ] && [ -n "$PREFERRED_BINARY" ]; then
  NATIVE_HEALTH_CACHE="$(t32_mcp_native_health_cache_path)"
  NATIVE_SIG="$(t32_mcp_native_signature "$PREFERRED_BINARY")"
  NATIVE_HEALTH_STATUS="$(t32_mcp_native_health_cached "$NATIVE_HEALTH_CACHE" "$NATIVE_SIG" || true)"
  if [ -z "$NATIVE_HEALTH_STATUS" ]; then
    if t32_mcp_native_health_probe "$PREFERRED_BINARY"; then
      NATIVE_HEALTH_STATUS="healthy"
    else
      NATIVE_HEALTH_STATUS="unhealthy"
    fi
    printf 'sig=%s\nstatus=%s\n' "$NATIVE_SIG" "$NATIVE_HEALTH_STATUS" >"$NATIVE_HEALTH_CACHE"
  fi
  if [ "$NATIVE_HEALTH_STATUS" = "healthy" ]; then
    RUNTIME="$PREFERRED_BINARY"
    RUNTIME_KIND="native"
  fi
fi

if [ -z "$RUNTIME" ] && [ -x "${REPO_ROOT}/src/compiler_rust/target/release/simple" ]; then
  RUNTIME="${REPO_ROOT}/src/compiler_rust/target/release/simple"
  RUNTIME_KIND="source-release"
elif [ -z "$RUNTIME" ] && [ -x "${REPO_ROOT}/src/compiler_rust/target/bootstrap/simple" ]; then
  RUNTIME="${REPO_ROOT}/src/compiler_rust/target/bootstrap/simple"
  RUNTIME_KIND="source-bootstrap"
elif [ -z "$RUNTIME" ] && [ -x "${SCRIPT_DIR}/simple" ]; then
  RUNTIME="${SCRIPT_DIR}/simple"
  RUNTIME_KIND="platform-release"
elif [ -z "$RUNTIME" ] && [ -x "${REPO_ROOT}/bin/simple" ]; then
  RUNTIME="${REPO_ROOT}/bin/simple"
  RUNTIME_KIND="bin-simple"
elif [ -z "$RUNTIME" ] && [ -x "${REPO_ROOT}/bin/release/simple" ]; then
  RUNTIME="${REPO_ROOT}/bin/release/simple"
  RUNTIME_KIND="bin-release-simple"
fi

T32_MCP_FRONTEND="${T32_MCP_FRONTEND:-full}"
COLD_ENTRY="${REPO_ROOT}/examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl"
TRACE32_ROOT="${REPO_ROOT}/examples/10_tooling/trace32_tools"
FULL_ENTRY="${REPO_ROOT}/examples/10_tooling/trace32_tools/t32_mcp/main.spl"
FULL_SIMPLE_LIB="${TRACE32_ROOT}"
COLD_SIMPLE_LIB="${TRACE32_ROOT}"
export SIMPLE_LOG=error
export SIMPLE_TIMEOUT_SECONDS=86400
export SIMPLE_MEMORY_LIMIT_MB=${SIMPLE_MEMORY_LIMIT_MB:-${SIMPLE_TEST_MEMORY_LIMIT_MB:-100}}

t32_mcp_compile_cached_entry() {
  t32_mcp_source_artifact="$1"
  t32_mcp_cache_file="$2"
  t32_mcp_simple_lib="$3"
  mkdir -p "$(dirname "$t32_mcp_cache_file")"
  if [ ! -f "$t32_mcp_cache_file" ] || [ "$t32_mcp_source_artifact" -nt "$t32_mcp_cache_file" ] || [ "$RUNTIME" -nt "$t32_mcp_cache_file" ]; then
    if [ "$DEBUG_ENABLED" = "1" ]; then
      t32_mcp_log_line "$WRAPPER_LOG" "compile_cache source=$t32_mcp_source_artifact cache=$t32_mcp_cache_file lib=$t32_mcp_simple_lib"
      SIMPLE_LIB="$t32_mcp_simple_lib" SIMPLE_BINARY="$RUNTIME" "$RUNTIME" compile "$t32_mcp_source_artifact" -o "$t32_mcp_cache_file" >>"$ERROR_LOG" 2>&1
    else
      SIMPLE_LIB="$t32_mcp_simple_lib" SIMPLE_BINARY="$RUNTIME" "$RUNTIME" compile "$t32_mcp_source_artifact" -o "$t32_mcp_cache_file" >>"$T32_MCP_STDERR_LOG" 2>&1
    fi
  fi
}

if [ -z "$RUNTIME" ]; then
  if [ "$DEBUG_ENABLED" = "1" ]; then
    t32_mcp_log_line "$WRAPPER_LOG" "runtime_choice=missing"
    t32_mcp_log_line "$ERROR_LOG" "error=no runtime found for t32_mcp"
  fi
  echo "error: no runtime found for t32_mcp" >&2
  exit 1
fi

if [ "$DEBUG_ENABLED" = "1" ]; then
  t32_mcp_log_line "$WRAPPER_LOG" "cwd=$(pwd)"
  t32_mcp_log_line "$WRAPPER_LOG" "repo_root=$REPO_ROOT"
  if [ "$NATIVE_REQUESTED" = "1" ] && [ -n "$PREFERRED_BINARY" ]; then
    t32_mcp_log_line "$WRAPPER_LOG" "native_preferred=1"
    t32_mcp_log_line "$WRAPPER_LOG" "native_binary=$PREFERRED_BINARY"
    t32_mcp_log_line "$WRAPPER_LOG" "native_health_cache=$NATIVE_HEALTH_CACHE"
    t32_mcp_log_line "$WRAPPER_LOG" "native_health=$NATIVE_HEALTH_STATUS"
  else
    t32_mcp_log_line "$WRAPPER_LOG" "native_preferred=0"
  fi
  t32_mcp_log_line "$WRAPPER_LOG" "runtime_choice=$RUNTIME_KIND"
  t32_mcp_log_line "$WRAPPER_LOG" "runtime=$RUNTIME"
  t32_mcp_log_line "$WRAPPER_LOG" "frontend_mode=$T32_MCP_FRONTEND"
  t32_mcp_log_line "$WRAPPER_LOG" "cold_entrypoint=$COLD_ENTRY"
  t32_mcp_log_line "$WRAPPER_LOG" "full_entrypoint=$FULL_ENTRY"
  t32_mcp_log_line "$WRAPPER_LOG" "daemon_dir=none"
  t32_mcp_log_line "$WRAPPER_LOG" "request_routing=$RUNTIME_KIND"
  t32_mcp_startup_log "wrapper_start runtime_kind=$RUNTIME_KIND runtime=$RUNTIME frontend=$T32_MCP_FRONTEND cwd=$(pwd)"
  export T32_MCP_DEBUG=1
  export T32_MCP_DEBUG_FILE="$FRONTEND_LOG"
fi

cd "$REPO_ROOT"
T32_MCP_STDERR_LOG="${REPO_ROOT}/.simple/logs/t32_mcp_stderr.log"
mkdir -p "$(dirname "$T32_MCP_STDERR_LOG")"

if [ "$RUNTIME_KIND" = "native" ]; then
  if [ "$DEBUG_ENABLED" = "1" ]; then
    t32_mcp_log_line "$WRAPPER_LOG" "request_routing=native"
    exec "$RUNTIME" "$@" 2>>"$ERROR_LOG"
  else
    exec "$RUNTIME" "$@" 2>>"$T32_MCP_STDERR_LOG"
  fi
fi

SOURCE_ARTIFACT="$COLD_ENTRY"
SOURCE_SIMPLE_LIB="$COLD_SIMPLE_LIB"
case "$T32_MCP_FRONTEND" in
  full)
    SOURCE_ARTIFACT="$FULL_ENTRY"
    SOURCE_SIMPLE_LIB="$FULL_SIMPLE_LIB"
    ;;
  cold|*)
    SOURCE_ARTIFACT="$COLD_ENTRY"
    ;;
esac

CACHE_ROOT="${REPO_ROOT}/.simple/cache/t32_mcp"
CACHE_FILE="${CACHE_ROOT}/${T32_MCP_FRONTEND}.smf"
if ! t32_mcp_compile_cached_entry "$SOURCE_ARTIFACT" "$CACHE_FILE" "$SOURCE_SIMPLE_LIB"; then
  if [ "$DEBUG_ENABLED" = "1" ]; then
    t32_mcp_log_line "$ERROR_LOG" "error=failed to compile cached frontend source=$SOURCE_ARTIFACT cache=$CACHE_FILE"
  fi
  echo "error: failed to compile cached t32_mcp frontend" >&2
  exit 1
fi
export SIMPLE_LIB="${SIMPLE_LIB:-$SOURCE_SIMPLE_LIB}"

if [ "$DEBUG_ENABLED" = "1" ]; then
  t32_mcp_startup_log "wrapper_exec runtime=$RUNTIME source_artifact=$SOURCE_ARTIFACT cache_file=$CACHE_FILE"
  exec "$RUNTIME" "$CACHE_FILE" "$@" 2>>"$ERROR_LOG"
fi

exec "$RUNTIME" "$CACHE_FILE" "$@" 2>>"$T32_MCP_STDERR_LOG"
T32_MCP_EOF
chmod +x "${mcp_release_dir}/t32_mcp_server"
echo "  t32_mcp_server"

cat > "${mcp_release_dir}/t32_lsp_mcp_server" <<'T32LSP_EOF'
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
REPO_ROOT=""
SEARCH_DIR="$SCRIPT_DIR"
while [ "$SEARCH_DIR" != "/" ]; do
  if [ -d "${SEARCH_DIR}/src" ] && [ -d "${SEARCH_DIR}/bin" ]; then
    REPO_ROOT="$SEARCH_DIR"
    break
  fi
  SEARCH_DIR="$(dirname "$SEARCH_DIR")"
done
if [ -z "$REPO_ROOT" ]; then
  echo "error: failed to locate repo root for t32_lsp_mcp" >&2
  exit 1
fi
RUNTIME="${SIMPLE_BINARY:-}"
if [ -n "$RUNTIME" ] && [ ! -x "$RUNTIME" ]; then RUNTIME=""; fi
if [ -z "$RUNTIME" ]; then RUNTIME="${SIMPLE_RUNTIME:-${REPO_ROOT}/src/compiler_rust/target/release/simple}"; fi
if [ ! -x "$RUNTIME" ]; then RUNTIME="${REPO_ROOT}/src/compiler_rust/target/bootstrap/simple"; fi
if [ ! -x "$RUNTIME" ]; then RUNTIME="${SCRIPT_DIR}/simple"; fi
if [ ! -x "$RUNTIME" ]; then RUNTIME="${REPO_ROOT}/bin/simple"; fi
if [ ! -x "$RUNTIME" ]; then RUNTIME="${REPO_ROOT}/bin/release/simple"; fi
ENTRY="${REPO_ROOT}/examples/10_tooling/trace32_tools/t32_lsp_mcp/main.spl"
TRACE32_ROOT="${REPO_ROOT}/examples/10_tooling/trace32_tools"
cd "$REPO_ROOT"
CWD="$(pwd)"
SUFFIX="$(printf '%s' "$CWD" | sed 's#^/*##; s#[^A-Za-z0-9._-]#_#g')"
if [ -z "$SUFFIX" ]; then SUFFIX="workspace"; fi
DEBUG_ENABLED=0
DEBUG_ROOT=""
WRAPPER_LOG=""
FRONTEND_LOG=""
REQUESTS_LOG=""
ERROR_LOG=""
if [ "${T32_LSP_MCP_DEBUG_LOG:-0}" != "0" ]; then
  DEBUG_ENABLED=1
  DEBUG_ROOT="${T32_LSP_MCP_DEBUG_ROOT:-/tmp/t32_lsp_mcp_debug_${SUFFIX}}"
  mkdir -p "$DEBUG_ROOT"
  WRAPPER_LOG="${DEBUG_ROOT}/wrapper.log"
  FRONTEND_LOG="${DEBUG_ROOT}/frontend.log"
  REQUESTS_LOG="${DEBUG_ROOT}/requests.log"
  ERROR_LOG="${DEBUG_ROOT}/errors.log"
  : > "$WRAPPER_LOG"
  : > "$FRONTEND_LOG"
  : > "$REQUESTS_LOG"
  : > "$ERROR_LOG"
  printf '%s runtime=%s entry=%s cwd=%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$RUNTIME" "$ENTRY" "$CWD" >>"$WRAPPER_LOG"
  export T32_LSP_MCP_DEBUG_FILE="$FRONTEND_LOG"
  export T32_LSP_MCP_REQUEST_LOG="$REQUESTS_LOG"
  export T32_LSP_MCP_ERROR_LOG="$ERROR_LOG"
fi
DAEMON_DIR="${T32_LSP_MCP_TOOL_DAEMON_DIR:-/tmp/t32_lsp_mcp_shared_${SUFFIX}}"
T32_LSP_MCP_STDERR_LOG="${REPO_ROOT}/.simple/logs/t32_lsp_mcp_stderr.log"
mkdir -p "$(dirname "$T32_LSP_MCP_STDERR_LOG")"
CACHE_ROOT="${REPO_ROOT}/.simple/cache/t32_lsp_mcp"
CACHE_FILE="${CACHE_ROOT}/main.smf"
TOOL_DAEMON_SOURCE="${REPO_ROOT}/examples/10_tooling/trace32_tools/cmm_lsp/mcp_daemon.spl"
TOOL_DAEMON_CACHE_FILE="${CACHE_ROOT}/mcp_daemon.smf"
TOOL_RUNNER_BIN_DEFAULT="${REPO_ROOT}/bin/release/t32_lsp_mcp_tool_runner"
mkdir -p "$CACHE_ROOT"
if [ ! -f "$CACHE_FILE" ] || [ "$ENTRY" -nt "$CACHE_FILE" ] || [ "$RUNTIME" -nt "$CACHE_FILE" ]; then
  rm -f "$CACHE_FILE"
  SIMPLE_LIB="$TRACE32_ROOT" SIMPLE_BINARY="$RUNTIME" SIMPLE_MEMORY_LIMIT_MB=512 SIMPLE_TIMEOUT_SECONDS=120 "$RUNTIME" compile "$ENTRY" -o "$CACHE_FILE" >>"$T32_LSP_MCP_STDERR_LOG" 2>&1 || true
fi
# Do not compile the optional daemon on startup. Claude waits on MCP health
# checks, and even a detached compile job can keep extra wrapper processes
# around long enough to look like a load failure. Tools can still use an
# existing cached daemon artifact when present, otherwise they fall back to
# the source entrypoint.
export SIMPLE_LIB="${SIMPLE_LIB:-$TRACE32_ROOT}"
export SIMPLE_RUNTIME="${SIMPLE_RUNTIME:-$RUNTIME}"
export T32_LSP_MCP_TOOL_RUNNER="${T32_LSP_MCP_TOOL_RUNNER:-examples/10_tooling/trace32_tools/t32_lsp_mcp/tool_runner.spl}"
if [ -x "$TOOL_RUNNER_BIN_DEFAULT" ]; then
  export T32_LSP_MCP_TOOL_RUNNER_BIN="${T32_LSP_MCP_TOOL_RUNNER_BIN:-$TOOL_RUNNER_BIN_DEFAULT}"
fi
if [ -f "$TOOL_DAEMON_CACHE_FILE" ]; then
  export T32_LSP_MCP_TOOL_DAEMON="${T32_LSP_MCP_TOOL_DAEMON:-$TOOL_DAEMON_CACHE_FILE}"
else
  export T32_LSP_MCP_TOOL_DAEMON="${T32_LSP_MCP_TOOL_DAEMON:-$TOOL_DAEMON_SOURCE}"
fi
export T32_LSP_MCP_TOOL_DAEMON_DIR="$DAEMON_DIR"
export SIMPLE_TIMEOUT_SECONDS=86400
export SIMPLE_MEMORY_LIMIT_MB=${SIMPLE_MEMORY_LIMIT_MB:-${SIMPLE_TEST_MEMORY_LIMIT_MB:-100}}
export SIMPLE_LOG="${SIMPLE_LOG:-error}"
MAIN_ARTIFACT="$CACHE_FILE"
if [ ! -f "$MAIN_ARTIFACT" ]; then MAIN_ARTIFACT="$ENTRY"; fi
if [ "$DEBUG_ENABLED" = "1" ]; then
  printf '%s cache=%s daemon_cache=%s runner_bin=%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$CACHE_FILE" "$TOOL_DAEMON_CACHE_FILE" "${T32_LSP_MCP_TOOL_RUNNER_BIN:-}" >>"$WRAPPER_LOG"
  RUST_LOG="${RUST_LOG:-error}" exec "${SIMPLE_RUNTIME:-$RUNTIME}" "$MAIN_ARTIFACT" "$@" 2>>"$ERROR_LOG"
fi
RUST_LOG="${RUST_LOG:-error}" exec "${SIMPLE_RUNTIME:-$RUNTIME}" "$MAIN_ARTIFACT" "$@" 2>>"$T32_LSP_MCP_STDERR_LOG"
T32LSP_EOF
chmod +x "${mcp_release_dir}/t32_lsp_mcp_server"
echo "  t32_lsp_mcp_server"

# Remove stale flat wrappers now that platform wrappers are canonical.
for stale_mcp in simple_mcp_server simple_lsp_mcp_server t32_mcp_server t32_lsp_mcp_server; do
  rm -f "${release_dir}/${stale_mcp}"
done

# Recreate bin/ symlinks to platform-specific release/ wrappers.
for mcp_name in simple_mcp_server simple_lsp_mcp_server t32_mcp_server t32_lsp_mcp_server; do
  mcp_link="${bin_dir}/${mcp_name}"
  if [ -L "${mcp_link}" ] || [ -f "${mcp_link}" ]; then
    rm -f "${mcp_link}"
  fi
  cd "${bin_dir}"
  case "${host_kernel}" in
    MINGW*|MSYS*|CYGWIN*) MSYS=winsymlinks:nativestrict ln -sf "release/${mcp_release_subdir}/${mcp_name}" "${mcp_name}" ;;
    *) ln -sf "release/${mcp_release_subdir}/${mcp_name}" "${mcp_name}" ;;
  esac
done
echo "  Linked bin/*_mcp_server → release/${mcp_release_subdir}/*"

if [ -f "${repo_root}/bin/codex_chrome_devtools_mcp.js" ]; then
  chmod +x "${repo_root}/bin/codex_chrome_devtools_mcp.js"
fi
if [ -f "${repo_root}/bin/codex_stitch_mcp.js" ]; then
  chmod +x "${repo_root}/bin/codex_stitch_mcp.js"
fi

if command -v codex >/dev/null 2>&1; then
  if command -v node >/dev/null 2>&1; then
    codex mcp remove chrome-devtools >/dev/null 2>&1 || true
    codex mcp add chrome-devtools -- node "${repo_root}/bin/codex_chrome_devtools_mcp.js" >/dev/null
    codex mcp remove stitch-mcp >/dev/null 2>&1 || true
    codex mcp add stitch-mcp -- node "${repo_root}/bin/codex_stitch_mcp.js" >/dev/null
    echo "Registered Codex MCP launchers globally: chrome-devtools, stitch-mcp"
  else
    echo "warning: node not found in PATH; Codex chrome/stitch MCP launchers will not start" >&2
  fi
elif command -v node >/dev/null 2>&1; then
  echo "Codex MCP launchers ready: bin/codex_chrome_devtools_mcp.js, bin/codex_stitch_mcp.js"
else
  echo "warning: node not found in PATH; Codex chrome/stitch MCP launchers will not start" >&2
fi

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

# ===========================================================================
# Run violation checker
# ===========================================================================

echo ""
violation_checker="${repo_root}/scripts/violation-checker.shs"
if [ -x "${violation_checker}" ]; then
  echo "Running violation checker..."
  echo ""
  "${violation_checker}" || true
else
  echo "(violation-checker.shs not found, skipping)"
fi

echo ""
echo "Setup complete."
