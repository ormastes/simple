#!/bin/sh
# Shared MCP server startup library — sourced by all 4 MCP wrappers.
# Provides: runtime resolution, compile cache, debug logging, native health probe.
#
# Usage (from a wrapper script):
#   . "${REPO_ROOT}/config/mcp/mcp_startup_lib.sh"
#
# Required before sourcing:
#   REPO_ROOT   — absolute path to repository root
#   MCP_SERVER  — server name slug (e.g. "simple_mcp", "t32_lsp_mcp")
#
# Optional before sourcing:
#   MCP_DEBUG_ENV    — env var name to check for debug mode (default: <MCP_SERVER upper>_DEBUG_LOG)
#   MCP_NATIVE_BIN   — path to native binary (skip native probe if empty)

# --- Utility ---

mcp_sanitize_segment() {
  printf '%s' "$1" | sed 's#^/*##; s#[^A-Za-z0-9._-]#_#g'
}

mcp_log_line() {
  _mcp_log_file="$1"; shift
  printf '%s %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')" "$*" >>"$_mcp_log_file"
}

# --- Symlink Resolution ---
# Call: mcp_resolve_self "$0"
# Sets: MCP_SCRIPT_DIR, MCP_REPO_ROOT (only if REPO_ROOT not already set)

mcp_find_repo_root_from() {
  _mcp_search_dir="$1"
  while [ "$_mcp_search_dir" != "/" ]; do
    if [ -d "${_mcp_search_dir}/src" ] && [ -d "${_mcp_search_dir}/bin" ]; then
      printf '%s' "$_mcp_search_dir"
      return 0
    fi
    _mcp_search_dir="$(dirname "$_mcp_search_dir")"
  done
  return 1
}

mcp_resolve_self() {
  _mcp_self="$1"
  while [ -L "$_mcp_self" ]; do
    _mcp_dir="$(cd "$(dirname "$_mcp_self")" && pwd)"
    _mcp_self="$(readlink "$_mcp_self")"
    case "$_mcp_self" in /*) ;; *) _mcp_self="${_mcp_dir}/${_mcp_self}" ;; esac
  done
  MCP_SCRIPT_DIR="$(cd "$(dirname "$_mcp_self")" && pwd)"
  if [ -z "${REPO_ROOT:-}" ]; then
    REPO_ROOT="$(mcp_find_repo_root_from "$MCP_SCRIPT_DIR")"
  fi
  if [ -z "${REPO_ROOT:-}" ]; then
    echo "error: failed to locate repo root for ${MCP_SERVER}" >&2
    exit 1
  fi
}

# --- Debug Logging ---
# Call: mcp_debug_init
# Reads: MCP_SERVER, MCP_DEBUG_ENV (optional)
# Sets: MCP_DEBUG_ENABLED, MCP_DEBUG_ROOT, MCP_WRAPPER_LOG, MCP_FRONTEND_LOG,
#       MCP_REQUESTS_LOG, MCP_ERROR_LOG

mcp_debug_init() {
  MCP_DEBUG_ENABLED=0
  MCP_DEBUG_ROOT=""
  MCP_WRAPPER_LOG=""
  MCP_FRONTEND_LOG=""
  MCP_REQUESTS_LOG=""
  MCP_ERROR_LOG=""

  _mcp_debug_var="${MCP_DEBUG_ENV:-}"
  if [ -z "$_mcp_debug_var" ]; then
    _mcp_debug_var="$(printf '%s' "$MCP_SERVER" | tr 'a-z' 'A-Z')_DEBUG_LOG"
  fi
  eval "_mcp_debug_val=\"\${${_mcp_debug_var}:-0}\""
  case "$_mcp_debug_val" in
    0|false|FALSE|no|NO|off|OFF) return 0 ;;
  esac

  MCP_DEBUG_ENABLED=1
  _mcp_cwd_seg="$(mcp_sanitize_segment "$(pwd)")"
  if [ -z "$_mcp_cwd_seg" ]; then _mcp_cwd_seg="workspace"; fi
  _mcp_custom_root_var="$(printf '%s' "$MCP_SERVER" | tr 'a-z' 'A-Z')_DEBUG_ROOT"
  eval "_mcp_custom_root=\"\${${_mcp_custom_root_var}:-}\""
  MCP_DEBUG_ROOT="${_mcp_custom_root:-/tmp/${MCP_SERVER}_debug_${_mcp_cwd_seg}}"
  mkdir -p "$MCP_DEBUG_ROOT"
  MCP_WRAPPER_LOG="${MCP_DEBUG_ROOT}/wrapper.log"
  MCP_FRONTEND_LOG="${MCP_DEBUG_ROOT}/frontend.log"
  MCP_REQUESTS_LOG="${MCP_DEBUG_ROOT}/requests.log"
  MCP_ERROR_LOG="${MCP_DEBUG_ROOT}/errors.log"
  : > "$MCP_WRAPPER_LOG"
  : > "$MCP_FRONTEND_LOG"
  : > "$MCP_REQUESTS_LOG"
  : > "$MCP_ERROR_LOG"
}

# --- Runtime Resolution ---
# Call: mcp_find_runtime
# Reads: REPO_ROOT, SIMPLE_BINARY (optional)
# Sets: MCP_RUNTIME, MCP_RUNTIME_KIND

mcp_find_runtime() {
  MCP_RUNTIME="${SIMPLE_BINARY:-}"
  MCP_RUNTIME_KIND=""
  if [ -n "$MCP_RUNTIME" ] && [ ! -x "$MCP_RUNTIME" ]; then MCP_RUNTIME=""; fi
  if [ -n "$MCP_RUNTIME" ]; then
    MCP_RUNTIME_KIND="env-simple-binary"
    return 0
  fi
  if [ -n "${MCP_SCRIPT_DIR:-}" ] && [ -x "${MCP_SCRIPT_DIR}/simple" ]; then
    MCP_RUNTIME="${MCP_SCRIPT_DIR}/simple"
    MCP_RUNTIME_KIND="platform-release"
  elif [ -x "${REPO_ROOT}/bin/simple" ]; then
    MCP_RUNTIME="${REPO_ROOT}/bin/simple"
    MCP_RUNTIME_KIND="bin-simple"
  elif [ -x "${REPO_ROOT}/src/compiler_rust/target/release/simple" ]; then
    MCP_RUNTIME="${REPO_ROOT}/src/compiler_rust/target/release/simple"
    MCP_RUNTIME_KIND="source-release"
  elif [ -x "${REPO_ROOT}/src/compiler_rust/target/bootstrap/simple" ]; then
    MCP_RUNTIME="${REPO_ROOT}/src/compiler_rust/target/bootstrap/simple"
    MCP_RUNTIME_KIND="source-bootstrap"
  fi
  if [ -z "$MCP_RUNTIME" ]; then
    echo "error: no runtime found for ${MCP_SERVER}" >&2
    exit 1
  fi
}

# --- Native Binary Health Probe ---
# Call: mcp_native_health_check "$native_bin_path"
# Sets: MCP_NATIVE_HEALTHY (0 or 1)

mcp_native_signature() {
  if stat -c '%Y:%s' "$1" >/dev/null 2>&1; then
    stat -c '%Y:%s' "$1"
  else
    stat -f '%m:%z' "$1"
  fi
}

mcp_native_health_check() {
  _mcp_native_bin="$1"
  MCP_NATIVE_HEALTHY=0

  if [ ! -x "$_mcp_native_bin" ]; then return 0; fi

  _mcp_cwd_seg="$(mcp_sanitize_segment "$(pwd)")"
  if [ -z "$_mcp_cwd_seg" ]; then _mcp_cwd_seg="workspace"; fi
  _mcp_health_cache="/tmp/${MCP_SERVER}_native_health_${_mcp_cwd_seg}.state"
  _mcp_sig="$(mcp_native_signature "$_mcp_native_bin")"

  # Check cached health
  if [ -f "$_mcp_health_cache" ]; then
    _mcp_cached_sig="$(sed -n 's/^sig=//p' "$_mcp_health_cache" | head -n 1)"
    _mcp_cached_status="$(sed -n 's/^status=//p' "$_mcp_health_cache" | head -n 1)"
    if [ "$_mcp_cached_sig" = "$_mcp_sig" ] && [ -n "$_mcp_cached_status" ]; then
      if [ "$_mcp_cached_status" = "healthy" ]; then MCP_NATIVE_HEALTHY=1; fi
      return 0
    fi
  fi

  # Probe: run --version with 2s timeout
  "$_mcp_native_bin" --version >/dev/null 2>&1 &
  _mcp_probe_pid=$!
  ( sleep 2; kill "$_mcp_probe_pid" >/dev/null 2>&1 || true ) &
  _mcp_killer_pid=$!
  if wait "$_mcp_probe_pid"; then
    _mcp_status="healthy"
    MCP_NATIVE_HEALTHY=1
  else
    _mcp_status="unhealthy"
  fi
  kill "$_mcp_killer_pid" >/dev/null 2>&1 || true
  wait "$_mcp_killer_pid" >/dev/null 2>&1 || true

  printf 'sig=%s\nstatus=%s\n' "$_mcp_sig" "$_mcp_status" >"$_mcp_health_cache"
}

# --- Compile Cache ---
# Call: mcp_compile_cached "$source" "$cache_file" "$simple_lib"
# Reads: MCP_RUNTIME, MCP_DEBUG_ENABLED, MCP_ERROR_LOG, MCP_WRAPPER_LOG
# Returns: 0 on success, 1 on failure
#
# On success, also writes a `<cache>.smf.ok` sentinel ONLY when:
#   - bin/simple compile exited 0
#   - the captured compile log has no `^warning: type check: Undefined` lines
#   - a short stdin-EOF probe of the SMF doesn't immediately error
# Without `.smf.ok`, mcp_exec_cached refuses to use the cached SMF.

mcp_compile_cached() {
  _mcp_source="$1"
  _mcp_cache="$2"
  _mcp_lib="$3"
  _mcp_ok="${_mcp_cache}.ok"
  mkdir -p "$(dirname "$_mcp_cache")"
  if [ -f "$_mcp_cache" ] && [ -f "$_mcp_ok" ] \
     && [ ! "$_mcp_source" -nt "$_mcp_cache" ] && [ ! "$MCP_RUNTIME" -nt "$_mcp_cache" ]; then
    return 0
  fi
  rm -f "$_mcp_cache" "$_mcp_ok"

  # Capture compile output to a tempfile so we can grep before promoting to .ok,
  # then append the same content to the persistent stderr log.
  _mcp_tmp_log="$(mktemp "${TMPDIR:-/tmp}/${MCP_SERVER}_compile.XXXXXX")" || return 1
  _mcp_persistent_log=""
  if [ "$MCP_DEBUG_ENABLED" = "1" ]; then
    _mcp_persistent_log="$MCP_ERROR_LOG"
    mcp_log_line "$MCP_WRAPPER_LOG" "compile_cache source=$_mcp_source cache=$_mcp_cache lib=$_mcp_lib"
  else
    _mcp_persistent_log="${REPO_ROOT}/.simple/logs/${MCP_SERVER}_stderr.log"
    mkdir -p "$(dirname "$_mcp_persistent_log")"
  fi

  SIMPLE_LIB="$_mcp_lib" SIMPLE_BINARY="$MCP_RUNTIME" SIMPLE_MEMORY_LIMIT_MB=512 SIMPLE_TIMEOUT_SECONDS=120 \
    "$MCP_RUNTIME" compile "$_mcp_source" -o "$_mcp_cache" </dev/null >"$_mcp_tmp_log" 2>&1
  _mcp_compile_rc=$?
  cat "$_mcp_tmp_log" >>"$_mcp_persistent_log" 2>/dev/null || true

  if [ "$_mcp_compile_rc" -ne 0 ]; then
    rm -f "$_mcp_tmp_log"
    return 1
  fi

  # Guard 1: refuse to promote on Undefined symbol warnings.
  if grep -E '^warning: type check: Undefined' "$_mcp_tmp_log" >/dev/null 2>&1; then
    if [ "$MCP_DEBUG_ENABLED" = "1" ] && [ -n "$MCP_WRAPPER_LOG" ]; then
      mcp_log_line "$MCP_WRAPPER_LOG" "compile_cache reject reason=undefined_symbol_warning cache=$_mcp_cache"
    fi
    rm -f "$_mcp_tmp_log"
    return 0
  fi

  # Guard 2: short startup probe — feed empty stdin under timeout. Reject if
  # the SMF immediately errors out (rt_interp_call / relocation failures).
  _mcp_probe_out="$(printf '' | timeout 3 "$MCP_RUNTIME" "$_mcp_cache" 2>&1)"
  _mcp_probe_rc=$?
  case "$_mcp_probe_out" in
    *"relocation failed"*|*"rt_interp_call: invalid"*|*"Undefined symbol"*|*"load failed"*)
      if [ "$MCP_DEBUG_ENABLED" = "1" ] && [ -n "$MCP_WRAPPER_LOG" ]; then
        mcp_log_line "$MCP_WRAPPER_LOG" "compile_cache reject reason=probe_runtime_error cache=$_mcp_cache rc=$_mcp_probe_rc"
      fi
      rm -f "$_mcp_tmp_log"
      return 0
      ;;
  esac
  # rc 0 (clean exit) or 124 (timeout while serving) are both acceptable;
  # anything else where probe_out is empty also acceptable.
  if [ "$_mcp_probe_rc" -ne 0 ] && [ "$_mcp_probe_rc" -ne 124 ] && [ -n "$_mcp_probe_out" ]; then
    if [ "$MCP_DEBUG_ENABLED" = "1" ] && [ -n "$MCP_WRAPPER_LOG" ]; then
      mcp_log_line "$MCP_WRAPPER_LOG" "compile_cache reject reason=probe_nonzero rc=$_mcp_probe_rc cache=$_mcp_cache"
    fi
    rm -f "$_mcp_tmp_log"
    return 0
  fi

  : > "$_mcp_ok"
  rm -f "$_mcp_tmp_log"
  return 0
}

# --- Exec with Cache ---
# Call: mcp_exec_cached "$entry" "$simple_lib" "$@"
# If a fresh cache exists, execs it immediately.
# If cache is stale/missing, execs source and kicks off background compile for next run.
# This avoids blocking the MCP health check with a slow compile.

mcp_exec_cached() {
  _mcp_entry="$1"
  _mcp_lib="$2"
  shift 2

  _mcp_cache_root="${REPO_ROOT}/.simple/cache/${MCP_SERVER}"
  _mcp_cache_file="${_mcp_cache_root}/main.smf"
  _mcp_cache_ok="${_mcp_cache_file}.ok"
  _mcp_stderr="${REPO_ROOT}/.simple/logs/${MCP_SERVER}_stderr.log"
  mkdir -p "$_mcp_cache_root" "$(dirname "$_mcp_stderr")"

  export SIMPLE_LIB="${SIMPLE_LIB:-$_mcp_lib}"
  export SIMPLE_RUNTIME="${SIMPLE_RUNTIME:-$MCP_RUNTIME}"
  export SIMPLE_TIMEOUT_SECONDS="${SIMPLE_TIMEOUT_SECONDS:-86400}"
  export SIMPLE_MEMORY_LIMIT_MB="${SIMPLE_MEMORY_LIMIT_MB:-${SIMPLE_TEST_MEMORY_LIMIT_MB:-100}}"
  export SIMPLE_LOG="${SIMPLE_LOG:-error}"

  # Opt-out: SIMPLE_MCP_DISABLE_CACHE=1 forces interpret-mode and skips
  # background compile entirely (avoids disk churn from repeated failed compiles).
  _mcp_disable_cache="${SIMPLE_MCP_DISABLE_CACHE:-0}"
  case "$_mcp_disable_cache" in
    1|true|TRUE|yes|YES|on|ON) _mcp_disable_cache=1 ;;
    *) _mcp_disable_cache=0 ;;
  esac

  # Use cached artifact ONLY if: exists, fresh, >1KB, AND has a `.smf.ok` sentinel
  # written by mcp_compile_cached (which gates on warnings + a startup probe).
  _mcp_artifact="$_mcp_entry"
  _mcp_cache_valid=0
  if [ "$_mcp_disable_cache" = "0" ] \
     && [ -f "$_mcp_cache_file" ] && [ -f "$_mcp_cache_ok" ] \
     && [ ! "$_mcp_entry" -nt "$_mcp_cache_file" ] && [ ! "$MCP_RUNTIME" -nt "$_mcp_cache_file" ]; then
    _mcp_cache_size=0
    if stat -c '%s' "$_mcp_cache_file" >/dev/null 2>&1; then
      _mcp_cache_size=$(stat -c '%s' "$_mcp_cache_file")
    else
      _mcp_cache_size=$(stat -f '%z' "$_mcp_cache_file")
    fi
    if [ "$_mcp_cache_size" -gt 1024 ]; then
      _mcp_cache_valid=1
      _mcp_artifact="$_mcp_cache_file"
    else
      rm -f "$_mcp_cache_file" "$_mcp_cache_ok"
    fi
  fi
  if [ "$_mcp_cache_valid" = "0" ] && [ "$_mcp_disable_cache" = "0" ]; then
    # Cache stale, missing, unverified, or corrupt — background compile for next startup
    (
      mcp_compile_cached "$_mcp_entry" "$_mcp_cache_file" "$_mcp_lib" || true
    ) &
  fi

  if [ "$MCP_DEBUG_ENABLED" = "1" ]; then
    mcp_log_line "$MCP_WRAPPER_LOG" "exec runtime=$MCP_RUNTIME artifact=$_mcp_artifact runtime_kind=$MCP_RUNTIME_KIND"
    RUST_LOG="${RUST_LOG:-error}" exec "$MCP_RUNTIME" "$_mcp_artifact" "$@" 2>>"$MCP_ERROR_LOG"
  fi
  RUST_LOG="${RUST_LOG:-error}" exec "$MCP_RUNTIME" "$_mcp_artifact" "$@" 2>>"$_mcp_stderr"
}
