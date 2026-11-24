#!/usr/bin/env bash
# ==============================================================================
# PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER
# Guarded by: scripts/check/fast-verify-bootstrap-scripts.shs
# ==============================================================================
# Unified Shared Cross-Platform Phased Build Script (Phase 3 & Phase 4)
# Shared across Linux, macOS, FreeBSD, SimpleOS, and Windows (MSYS2 / Git-Bash).

set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
DEFAULT_SOURCE_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/../.." && pwd -P)

STAGE3_POLICY_SDN="$SCRIPT_DIR/stage3-native-host-link-policy.sdn"
export STAGE3_POLICY_SDN
. "$SCRIPT_DIR/stage3-native-host-link-policy.shs"
. "$SCRIPT_DIR/lib/run-timeout.shs"

PHASE=""
FORCE_MENU=0
COMPILE_MODE="${SIMPLE_P3_COMPILE_MODE:-shard}"
LINK_MODE="${SIMPLE_P3_LINK_MODE:-dynlib}"
P4_LINK_MODE="${SIMPLE_P4_LINK_MODE:-dynload}"
WIN_CONFIG="${SIMPLE_WIN_CONFIG:-mingw}"
TARGET_ARG=""
BACKEND="llvm"
BACKEND_PLUGIN="${SIMPLE_BACKEND_PLUGIN:-}"
THREADS=""
SOURCE_ROOT="$DEFAULT_SOURCE_ROOT"
BUILD_ROOT=""
RUNTIME_PATH=""
P2_BIN=""
P3A_BIN=""
P3A_EXPLICIT=0
P3A_SHA256=""
P3B_CACHE_FROM=""
P3B_BIN=""
MEM_GUARD_SCRIPT="${SIMPLE_MEM_GUARD_SCRIPT:-}"
INTERNAL_LINKER_GATE="auto"
NON_INTERACTIVE=0
DRY_RUN=0
PATH_CHECK=0

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/build-phase3-phase4.sh [OPTIONS]

Shared cross-platform Phase 3 & Phase 4 build script (Linux, macOS, FreeBSD, Windows).

Options:
  --menu                         Show interactive Phased Build Menu
  --phase=p3a|p3b|p3|p4|all      Select phase non-interactively
  --compile-mode=shard|file      Phase 3 compile mode (DEFAULT: shard; optional: file)
  --p3-compile-mode=shard|file   Alias for --compile-mode
  --link-mode=dynlib|one-binary  Phase 3 unit link mode (DEFAULT: dynlib + static primitive archive)
  --p4-link-mode=dynload|one-binary  Phase 4 CLI link mode (DEFAULT: dynload)
  --win-config=mingw|msvc        Windows toolchain config (DEFAULT: mingw; optional: msvc)
  --target=<triple>              Target triple (checked against host via native_host_match tag)
  --backend=llvm|cranelift       Compiler backend (default: llvm)
  --backend-plugin=<FILE>        Optional pre-built backend plugin dynlib to load via --backend-plugin
  --threads=<N>                  Parallel worker threads (default: host CPU count)
  --source-root=<DIR>            Repository checkout root
  --build-root=<DIR>             Build output directory (default: <source-root>/build/phased-selfhost)
  --seed-dir=<DIR>               Runtime directory containing libsimple_runtime.a (alias: --runtime-path)
  --runtime-path=<DIR>           Runtime directory containing libsimple_runtime.a
  --p2-bin=<FILE>                Compatible minimal producer (Phase 2 or later; bind actual provenance)
  --p3a-bin=<FILE>               Existing qualified P3a (required for --phase=p3b)
  --p3b-cache-from=<DIR>         Copy a stopped Linux P3b build cache into the fresh build root
  --p3a-sha256=<HEX>             Exact P3a bytes; caller verifies source/runtime/Hello provenance
  --p3b-bin=<FILE>               Existing Phase 3b compiler binary (when running --phase=p4)
  --mem-guard=<FILE>             Optional mem-guard-watchdog.sh script to wrap builds
  --with-internal-linker-gate    Enable SIMPLE_LINKER=internal verification gate
  --no-internal-linker-gate      Skip SIMPLE_LINKER=internal verification gate
  --non-interactive, --yes       Never prompt or pause
  --dry-run                      Validate policy and print environment + commands without building
  --path-check                   Verify alive action traversal without running heavy builds
  --simulate-host=<plat>-<cpu>   Simulate host <linux|macos|freebsd|windows|simpleos>-<x86_64|aarch64|riscv64>
  --help, -h                     Show this help message
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --menu) FORCE_MENU=1; shift ;;
    --phase) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; PHASE=$2; shift 2 ;;
    --phase=*) PHASE=${1#*=}; shift ;;
    --compile-mode|--p3-compile-mode) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; COMPILE_MODE=$2; shift 2 ;;
    --compile-mode=*|--p3-compile-mode=*) COMPILE_MODE=${1#*=}; shift ;;
    --link-mode) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; LINK_MODE=$2; shift 2 ;;
    --link-mode=*) LINK_MODE=${1#*=}; shift ;;
    --p4-link-mode) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; P4_LINK_MODE=$2; shift 2 ;;
    --p4-link-mode=*) P4_LINK_MODE=${1#*=}; shift ;;
    --win-config) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; WIN_CONFIG=$2; shift 2 ;;
    --win-config=*) WIN_CONFIG=${1#*=}; shift ;;
    --mingw|/mingw|-mingw) WIN_CONFIG="mingw"; shift ;;
    --msvc|/msvc|-msvc) WIN_CONFIG="msvc"; shift ;;
    --target) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; TARGET_ARG=$2; shift 2 ;;
    --target=*) TARGET_ARG=${1#*=}; shift ;;
    --backend) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; BACKEND=$2; shift 2 ;;
    --backend=*) BACKEND=${1#*=}; shift ;;
    --backend-plugin) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; BACKEND_PLUGIN=$2; shift 2 ;;
    --backend-plugin=*) BACKEND_PLUGIN=${1#*=}; shift ;;
    --threads|--jobs) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; THREADS=$2; shift 2 ;;
    --threads=*|--jobs=*) THREADS=${1#*=}; shift ;;
    --source-root) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; SOURCE_ROOT=$2; shift 2 ;;
    --source-root=*) SOURCE_ROOT=${1#*=}; shift ;;
    --build-root) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; BUILD_ROOT=$2; shift 2 ;;
    --build-root=*) BUILD_ROOT=${1#*=}; shift ;;
    --seed-dir|--runtime-path) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; RUNTIME_PATH=$2; shift 2 ;;
    --seed-dir=*|--runtime-path=*) RUNTIME_PATH=${1#*=}; shift ;;
    --p2-bin) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; P2_BIN=$2; shift 2 ;;
    --p2-bin=*) P2_BIN=${1#*=}; shift ;;
    --p3a-bin) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; P3A_BIN=$2; P3A_EXPLICIT=1; shift 2 ;;
    --p3a-bin=*) P3A_BIN=${1#*=}; P3A_EXPLICIT=1; shift ;;
    --p3a-sha256) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; P3A_SHA256=$2; shift 2 ;;
    --p3a-sha256=*) P3A_SHA256=${1#*=}; shift ;;
    --p3b-cache-from) [ "$#" -ge 2 ] && [ -n "$2" ] || { usage >&2; exit 2; }; P3B_CACHE_FROM=$2; shift 2 ;;
    --p3b-cache-from=) usage >&2; exit 2 ;;
    --p3b-cache-from=*) P3B_CACHE_FROM=${1#*=}; shift ;;
    --p3b-bin) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; P3B_BIN=$2; shift 2 ;;
    --p3b-bin=*) P3B_BIN=${1#*=}; shift ;;
    --mem-guard) [ "$#" -ge 2 ] || { usage >&2; exit 2; }; MEM_GUARD_SCRIPT=$2; shift 2 ;;
    --mem-guard=*) MEM_GUARD_SCRIPT=${1#*=}; shift ;;
    --with-internal-linker-gate) INTERNAL_LINKER_GATE="1"; shift ;;
    --no-internal-linker-gate) INTERNAL_LINKER_GATE="0"; shift ;;
    --non-interactive|--yes) NON_INTERACTIVE=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --path-check) PATH_CHECK=1; shift ;;
    --simulate-host)
      [ "$#" -ge 2 ] || { usage >&2; exit 2; }
      STAGE3_SIMULATE_HOST=$2; export STAGE3_SIMULATE_HOST; shift 2 ;;
    --simulate-host=*)
      STAGE3_SIMULATE_HOST=${1#*=}; export STAGE3_SIMULATE_HOST; shift ;;
    --help|-h) usage; exit 0 ;;
    *) echo "ERROR: unknown option '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

case "$WIN_CONFIG" in
  mingw|gnu) WIN_CONFIG="mingw" ;;
  msvc) WIN_CONFIG="msvc" ;;
  *) echo "ERROR: invalid --win-config='$WIN_CONFIG' (expected mingw or msvc)" >&2; exit 2 ;;
esac

case "$COMPILE_MODE" in
  shard|phase) COMPILE_MODE="shard" ;;
  file) COMPILE_MODE="file" ;;
  *) echo "ERROR: invalid --compile-mode='$COMPILE_MODE' (expected shard or file)" >&2; exit 2 ;;
esac

case "$LINK_MODE" in
  dynlib|one-binary) ;;
  *) echo "ERROR: invalid --link-mode='$LINK_MODE' (expected dynlib or one-binary)" >&2; exit 2 ;;
esac

case "$P4_LINK_MODE" in
  dynload|one-binary) ;;
  *) echo "ERROR: invalid --p4-link-mode='$P4_LINK_MODE' (expected dynload or one-binary)" >&2; exit 2 ;;
esac

case "$BACKEND" in
  llvm|cranelift) ;;
  *) echo "ERROR: invalid --backend='$BACKEND' (expected llvm or cranelift)" >&2; exit 2 ;;
esac

# Enforce platform/CPU policy and mandatory native_host_match tag check.
stage3_apply_native_host_link_policy "$TARGET_ARG" "$COMPILE_MODE" "$WIN_CONFIG" "$LINK_MODE"

if [ -n "$BACKEND_PLUGIN" ]; then
  if [ "${SIMPLE_STAGE3_ALLOW_EXISTING_DYNLIBS:-1}" = "0" ]; then
    echo "STAGE3-E-DYNLIB-LOAD-DISABLED: SIMPLE_STAGE3_ALLOW_EXISTING_DYNLIBS=0 forbids --backend-plugin" >&2
    exit 2
  fi
  if [ "$PATH_CHECK" -eq 0 ] && [ "$DRY_RUN" -eq 0 ] && [ ! -f "$BACKEND_PLUGIN" ]; then
    echo "STAGE3-E-BACKEND-PLUGIN-MISSING: --backend-plugin file does not exist: $BACKEND_PLUGIN" >&2
    exit 2
  fi
fi

if [ "$STAGE3_HOST_PLATFORM" = "windows" ]; then
  WIN_DISPLAY="$WIN_CONFIG"
  EXE_EXT=".exe"
else
  WIN_DISPLAY="n/a"
  EXE_EXT=""
fi

if [ "$INTERNAL_LINKER_GATE" = "auto" ]; then
  if [ "$STAGE3_HOST_PLATFORM" = "darwin" ]; then
    INTERNAL_LINKER_GATE="1"
  else
    INTERNAL_LINKER_GATE="0"
  fi
fi

detect_default_threads() {
  if [ -n "$THREADS" ]; then
    printf '%s\n' "$THREADS"
    return 0
  fi
  t_cnt=""
  case "$STAGE3_HOST_PLATFORM" in
    darwin|freebsd)
      if t_cnt=$(sysctl -n hw.ncpu 2>/dev/null); then :; else t_cnt=""; fi
      ;;
    linux)
      if t_cnt=$(nproc 2>/dev/null); then :; elif t_cnt=$(getconf _NPROCESSORS_ONLN 2>/dev/null); then :; else t_cnt=""; fi
      ;;
    windows) t_cnt="${NUMBER_OF_PROCESSORS:-}" ;;
  esac
  case "$t_cnt" in
    ''|*[!0-9]*|0) t_cnt=4 ;;
  esac
  printf '%s\n' "$t_cnt"
}

THREADS=$(detect_default_threads)
BUILD_ROOT="${BUILD_ROOT:-$SOURCE_ROOT/build/phased-selfhost}"
RUNTIME_PATH="${RUNTIME_PATH:-$BUILD_ROOT/seed/runtime}"
P2_BIN="${P2_BIN:-$BUILD_ROOT/phase2/simple${EXE_EXT}}"
P3A_DIR="$BUILD_ROOT/phase3-a"
P3A_BIN="${P3A_BIN:-$P3A_DIR/simple${EXE_EXT}}"
P3B_DIR="$BUILD_ROOT/phase3-b"
P3B_BIN="${P3B_BIN:-$P3B_DIR/simple${EXE_EXT}}"
P4_DIR="$BUILD_ROOT/p4-from-p3b"
LOG_DIR="$BUILD_ROOT/logs"

show_phased_menu() {
  cat <<EOF
============================================================
  Simple Self-Hosted Phased Build (Phase 3 / Phase 4)
  Host: ${STAGE3_HOST_TAG} | Target: ${STAGE3_RESOLVED_TARGET} [native_host_match=PASS]
  Windows Config: ${WIN_DISPLAY} | P3 Compile: ${COMPILE_MODE}
============================================================
  1) Phase 3a only          (P2 -> P3a, ${COMPILE_MODE} compile + dynlib/static-primitive link)
  2) Phase 3a + 3b verify   (P2 -> P3a -> P3b + internal linker gate)
  3) Phase 4 only           (P3b -> P4 release + debug-xray + Stage 5 essentials)
  4) Full Phase 3 + Phase 4 (P2 -> P3a -> P3b -> P4 all)
  5) Phase 3 (file-based parallel option: --compile-mode=file)
  6) Phase 3 (phased HIR/MIR shard option: --compile-mode=shard)
  0) Exit
============================================================
EOF
  printf 'Select phased build option [0-6]: '
  choice=""
  read -r choice || choice="0"
  case "$choice" in
    1) PHASE="p3a" ;;
    2) PHASE="p3" ;;
    3) PHASE="p4" ;;
    4) PHASE="all" ;;
    5) PHASE="p3"; COMPILE_MODE="file"; stage3_apply_native_host_link_policy "$TARGET_ARG" "$COMPILE_MODE" "$WIN_CONFIG" "$LINK_MODE" ;;
    6) PHASE="p3"; COMPILE_MODE="shard"; stage3_apply_native_host_link_policy "$TARGET_ARG" "$COMPILE_MODE" "$WIN_CONFIG" "$LINK_MODE" ;;
    0|"") echo "Exiting phased build menu."; exit 0 ;;
    *) echo "ERROR: invalid menu choice '$choice'" >&2; exit 2 ;;
  esac
}

if [ "$FORCE_MENU" -eq 1 ]; then
  show_phased_menu
elif [ -z "$PHASE" ]; then
  if [ "$PATH_CHECK" -eq 1 ] || [ "$DRY_RUN" -eq 1 ]; then
    PHASE="all"
  elif [ "$NON_INTERACTIVE" -eq 0 ] && [ -t 0 ]; then
    show_phased_menu
  else
    echo "ERROR: --phase=p3a|p3b|p3|p4|all is required in non-interactive mode (or pass --menu / --path-check / --dry-run)." >&2
    exit 2
  fi
fi

case "$PHASE" in
  p3a|p3b|p3|p4|all) ;;
  *) echo "ERROR: invalid --phase='$PHASE' (expected p3a, p3b, p3, p4, or all)" >&2; exit 2 ;;
esac

# Only the standalone continuation may override the P3a producer. In p3/all
# that path is an output and must retain its established build-root ownership.
if [ "$PHASE" != p3b ] && { [ "$P3A_EXPLICIT" -eq 1 ] || [ -n "$P3A_SHA256" ]; }; then
  echo "ERROR: --p3a-bin/--p3a-sha256 require --phase=p3b" >&2; exit 2
fi
if [ "$PHASE" = p3b ]; then
  [ "$P3A_EXPLICIT" -eq 1 ] && [ -n "$P3A_BIN" ] || { echo 'ERROR: standalone P3b requires explicit --p3a-bin' >&2; exit 2; }
  case "$P3A_SHA256" in ''|*[!0-9a-f]*) echo 'ERROR: P3b requires an exact lowercase P3a SHA-256' >&2; exit 2 ;; esac
  [ "${#P3A_SHA256}" -eq 64 ] || { echo 'ERROR: P3a SHA-256 must have 64 digits' >&2; exit 2; }
fi

if [ -n "$P3B_CACHE_FROM" ] && { [ "$PHASE" != p3b ] || [ "$(uname -s)" != Linux ]; }; then
  echo 'ERROR: --p3b-cache-from requires Linux and --phase=p3b' >&2; exit 2
fi

PATH_ACTION_COUNT=0

emit_path_action() {
  pa_phase=$1
  pa_step=$2
  pa_cmode=$3
  pa_lmode=$4
  pa_xray=$5
  pa_rel=$6
  PATH_ACTION_COUNT=$((PATH_ACTION_COUNT + 1))
  printf 'PATH_ACTION|script=build-phase3-phase4.sh|platform=%s|cpu=%s|win_config=%s|phase=%s|step=%s|compile_mode=%s|link_mode=%s|xray=%s|release=%s|status=ALIVE\n' \
    "$STAGE3_HOST_PLATFORM" "$STAGE3_HOST_CPU" "$WIN_DISPLAY" "$pa_phase" "$pa_step" "$pa_cmode" "$pa_lmode" "$pa_xray" "$pa_rel"
}

run_path_check() {
  PATH_ACTION_COUNT=0
  p4_lmode_label="$LINK_MODE"
  if [ "$P4_LINK_MODE" = "one-binary" ]; then
    p4_lmode_label="one-binary"
  else
    p4_lmode_label="dynlib"
  fi

  emit_path_action "init" "native-host-match-check" "$COMPILE_MODE" "$LINK_MODE" "0" "0"

  case "$PHASE" in
    p3a|p3|all)
      emit_path_action "p3a" "compile-bootstrap-stage3" "$COMPILE_MODE" "$LINK_MODE" "0" "0"
      emit_path_action "p3a" "verify-dynlib-units-no-extra-backends" "$COMPILE_MODE" "$LINK_MODE" "0" "0"
      emit_path_action "p3a" "hello-smoke" "$COMPILE_MODE" "one-binary" "0" "0"
      ;;
  esac

  case "$PHASE" in
    p3b|p3|all)
      emit_path_action "p3b" "compile-bootstrap-stage3-selfhost" "$COMPILE_MODE" "$LINK_MODE" "0" "0"
      emit_path_action "p3b" "verify-dynlib-units-no-extra-backends" "$COMPILE_MODE" "$LINK_MODE" "0" "0"
      emit_path_action "p3b" "hello-smoke" "$COMPILE_MODE" "one-binary" "0" "0"
      if [ "$INTERNAL_LINKER_GATE" = "1" ]; then
        emit_path_action "p3b" "internal-linker-gate" "$COMPILE_MODE" "one-binary" "0" "0"
      fi
      ;;
  esac

  if [ "$PHASE" = p4 ]; then
    emit_path_action "p4" "producer-hello-smoke" "$COMPILE_MODE" "one-binary" "0" "0"
  fi

  case "$PHASE" in
    p4|all)
      emit_path_action "p4" "cli-release" "$COMPILE_MODE" "$p4_lmode_label" "0" "1"
      emit_path_action "p4" "cli-debug-xray" "$COMPILE_MODE" "$p4_lmode_label" "1" "0"
      emit_path_action "p4" "stage5-simple_test_runner" "$COMPILE_MODE" "one-binary" "0" "1"
      emit_path_action "p4" "stage5-simple_build_runner" "$COMPILE_MODE" "one-binary" "0" "1"
      emit_path_action "p4" "stage5-simple_mcp_server" "$COMPILE_MODE" "one-binary" "0" "1"
      emit_path_action "p4" "stage5-simple_lsp_mcp_server" "$COMPILE_MODE" "one-binary" "0" "1"
      if [ "$INTERNAL_LINKER_GATE" = "1" ]; then
        emit_path_action "p4" "cli-internal-linker" "$COMPILE_MODE" "one-binary" "0" "1"
      fi
      emit_path_action "p4" "smoke-gates" "$COMPILE_MODE" "$p4_lmode_label" "1" "1"
      ;;
  esac

  printf 'PATH_SUMMARY|script=build-phase3-phase4.sh|platform=%s|cpu=%s|target=%s|actions=%s|status=PASS\n' \
    "$STAGE3_HOST_PLATFORM" "$STAGE3_HOST_CPU" "$STAGE3_RESOLVED_TARGET" "$PATH_ACTION_COUNT"
}

if [ "$PATH_CHECK" -eq 1 ]; then
  run_path_check
  exit 0
fi

if [ "$DRY_RUN" -eq 1 ]; then
  echo "# === DRY-RUN: scripts/bootstrap/build-phase3-phase4.sh ==="
  echo "HOST_TAG=$STAGE3_HOST_TAG"
  echo "TARGET=$STAGE3_RESOLVED_TARGET"
  echo "NATIVE_HOST_MATCH=true"
  echo "WIN_CONFIG=$WIN_DISPLAY"
  echo "PHASE=$PHASE"
  echo "COMPILE_MODE=$COMPILE_MODE"
  echo "LINK_MODE=$LINK_MODE"
  echo "P4_LINK_MODE=$P4_LINK_MODE"
  echo "THREADS=$THREADS"
  stage3_print_policy_env "$STAGE3_RESOLVED_TARGET" "$COMPILE_MODE" "$WIN_CONFIG" "$LINK_MODE"
  if [ "$STAGE3_HOST_PLATFORM" = "windows" ] && [ "$WIN_CONFIG" = "msvc" ]; then
    echo 'export CL="/TC"'
    echo 'export MSYS2_ENV_CONV_EXCL="CL="'
  fi
  dry_p3_sources="--source $STAGE3_POLICY_K1_ROOT --source $STAGE3_POLICY_HOST_COMP_ROOT --source src/compiler --source src/app --source src/lib"
  if [ "${SIMPLE_STAGE3_BUILD_EXTRA_DYNLIBS:-0}" = "1" ]; then
    dry_p3_sources="$dry_p3_sources --source src/plugins"
  fi
  dry_plugin_arg=""
  if [ -n "$BACKEND_PLUGIN" ]; then
    dry_plugin_arg=" --backend-plugin $BACKEND_PLUGIN"
  fi
  case "$PHASE" in
    p3a|p3|all)
      p3_mode_flag="dynload"
      [ "$LINK_MODE" = "one-binary" ] && p3_mode_flag="one-binary"
      echo "CMD_P3A: $P2_BIN native-build --target $STAGE3_RESOLVED_TARGET --backend $BACKEND --runtime-bundle core-c-bootstrap $dry_p3_sources --entry-closure${dry_plugin_arg} --threads $THREADS --cache-dir $P3A_DIR/cache --mode $p3_mode_flag --runtime-path $RUNTIME_PATH --entry src/app/cli/bootstrap_main.spl -o $P3A_BIN"
      ;;
  esac
  case "$PHASE" in
    p3b|p3|all)
      p3_mode_flag="dynload"
      [ "$LINK_MODE" = "one-binary" ] && p3_mode_flag="one-binary"
      echo "CMD_P3B: $P3A_BIN native-build --target $STAGE3_RESOLVED_TARGET --backend $BACKEND --runtime-bundle core-c-bootstrap $dry_p3_sources --entry-closure${dry_plugin_arg} --threads $THREADS --cache-dir $P3B_DIR/cache --mode $p3_mode_flag --runtime-path $RUNTIME_PATH --entry src/app/cli/bootstrap_main.spl -o $P3B_BIN"
      ;;
  esac
  case "$PHASE" in
    p4|all)
      echo "CMD_P4_RELEASE: $P3B_BIN native-build --target $STAGE3_RESOLVED_TARGET --backend $BACKEND --runtime-bundle core-c-bootstrap --source src/compositions/cuda_disabled --source src/compiler --source src/app --source src/lib --source src/os --source src/plugins --entry-closure${dry_plugin_arg} --profile=prod --release --strip --threads $THREADS --cache-dir $P4_DIR/cli-release/cache --mode $P4_LINK_MODE --entry src/app/cli/main.spl --runtime-path $RUNTIME_PATH -o $P4_DIR/bin/simple${EXE_EXT}"
      echo "CMD_P4_DEBUG_XRAY: $P3B_BIN native-build --target $STAGE3_RESOLVED_TARGET --backend $BACKEND --runtime-bundle core-c-bootstrap --source src/compositions/cuda_disabled --source src/compiler --source src/app --source src/lib --source src/os --source src/plugins --entry-closure${dry_plugin_arg} --profile=dev --debug --no-strip --xray --threads $THREADS --cache-dir $P4_DIR/cli-debug/cache --mode $P4_LINK_MODE --entry src/app/cli/main.spl --runtime-path $RUNTIME_PATH -o $P4_DIR/bin/simple-debug${EXE_EXT}"
      ;;
  esac
  exit 0
fi

# Live execution helpers
if [ -n "$MEM_GUARD_SCRIPT" ] && [ -f "$MEM_GUARD_SCRIPT" ]; then
  . "$MEM_GUARD_SCRIPT"
fi

apply_windows_toolchain_env() {
  if [ "$STAGE3_HOST_PLATFORM" = "windows" ]; then
    export OS="${OS:-Windows_NT}"
    if [ "$WIN_CONFIG" = "msvc" ]; then
      export SIMPLE_WINDOWS_ABI="msvc"
      export SIMPLE_LINKER_FLAVOR="msvc"
      export CL="/TC"
      case ";${MSYS2_ENV_CONV_EXCL:-};" in
        *";CL="*) ;;
        *) export MSYS2_ENV_CONV_EXCL="${MSYS2_ENV_CONV_EXCL:+${MSYS2_ENV_CONV_EXCL};}CL=" ;;
      esac
    else
      export SIMPLE_WINDOWS_ABI="gnu"
      export SIMPLE_LINKER_FLAVOR="gnu"
    fi
  fi
}

run_guarded_cmd() {
  rg_label=$1
  rg_log=$2
  shift 2
  if command -v run_with_mem_guard >/dev/null 2>&1; then
    run_with_mem_guard "$rg_label" "$rg_log" "$@"
  else
    (
      for rg_k in $(env | awk -F= '/^[A-Za-z_][A-Za-z0-9_]*=/{print $1}'); do
        case "$rg_k" in
          HOME|USER|LOGNAME|SHELL|PATH|TMPDIR|TMP|TEMP|LANG|LC_ALL|LC_CTYPE|TZ|TERM|CI|PWD|OLDPWD|SHLVL|_) ;;
          CC|CXX|CFLAGS|CPATH|LIBRARY_PATH|SDKROOT|DEVELOPER_DIR|MACOSX_DEPLOYMENT_TARGET|HOMEBREW_PREFIX) ;;
          LLVM_PREFIX|LLVM_SYS_231_PREFIX|LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING|RUST_LOG) ;;
          MALLOC_ARENA_MAX|MALLOC_TRIM_THRESHOLD_|XDG_CACHE_HOME) ;;
          SYSTEMROOT|WINDIR|COMSPEC|PATHEXT|OS|INCLUDE|LIB|LIBPATH|CL|MSYS2_ENV_CONV_EXCL|MSYS2_ARG_CONV_EXCL) ;;
          SIMPLE_*) ;;
          *)
            if unset "$rg_k" 2>/dev/null; then
              :
            fi
            ;;
        esac
      done
      exec "$@"
    ) >"$rg_log" 2>&1
  fi
}

sign_stage_outputs() {
  ss_dir=$1
  ss_bin=$2
  if [ "$STAGE3_HOST_PLATFORM" = "darwin" ] && command -v codesign >/dev/null 2>&1; then
    if [ -d "$ss_dir/lib" ]; then
      for dylib in "$ss_dir/lib/"*.dylib; do
        [ -f "$dylib" ] || continue
        codesign -s - --force "$dylib"
      done
    fi
    codesign -s - --force "$ss_bin"
  fi
  if chmod 0755 "$ss_bin" 2>/dev/null; then :; fi
}

verify_stage3_dynlibs() {
  vs_label=$1
  vs_dir=$2
  if [ "$LINK_MODE" != "dynlib" ] || [ "$STAGE3_HOST_PLATFORM" = "windows" ] || [ "${SIMPLE_STAGE3_BUILD_EXTRA_DYNLIBS:-0}" = "1" ]; then
    return 0
  fi
  for bad_lib in "$vs_dir"/lib/libbackend_* "$vs_dir"/lib/*cuda* "$vs_dir"/lib/*vulkan*; do
    if [ -e "$bad_lib" ]; then
      echo "ERROR: [$vs_label] Unneeded non-native dynlib built in Stage 3: $bad_lib" >&2
      return 1
    fi
  done
  return 0
}

# Exact candidate execution gate: a banner alone cannot authorize a dependent phase.
run_stage3_hello() (
  s3h_label=$1
  s3h_candidate=$2
  s3h_dir=$3/hello
  case "$(uname -s)" in
    MSYS*|MINGW*|CYGWIN*) ;; # shared helper owns the native-child watchdog
    *) command -v timeout >/dev/null 2>&1 || command -v gtimeout >/dev/null 2>&1 || {
      echo "ERROR: [$s3h_label] bounded Hello execution requires timeout or gtimeout" >&2
      return 1
    } ;;
  esac
  mkdir -p "$s3h_dir/cache" "$s3h_dir/tmp" || return $?
  s3h_source="test/04_smoke/bootstrap_hello_world.spl"
  s3h_out="$s3h_dir/hello${EXE_EXT}"
  rm -f "$s3h_out" "$s3h_dir/stdout" "$s3h_dir/expected"
  # Frozen tracked fixture is admitted by the source inventory; external generated
  # entries are refused by the shard source-authority gate.
  [ -f "$SOURCE_ROOT/$s3h_source" ] || return 1
  printf 'hello\n' >"$s3h_dir/expected"
  cd "$SOURCE_ROOT" || return $?
  stage3_apply_native_host_link_policy "$STAGE3_RESOLVED_TARGET" "$COMPILE_MODE" "$WIN_CONFIG" one-binary || return $?
  apply_windows_toolchain_env || return $?
  unset SIMPLE_BOOTSTRAP SIMPLE_BOOTSTRAP_STAGE3 SIMPLE_BOOTSTRAP_STAGE4 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM SIMPLE_FILE_WORKERS
  export SIMPLE_BINARY="$s3h_candidate"
  export SIMPLE_PROJECT_ROOT="$SOURCE_ROOT"
  export SIMPLE_LIB="$SOURCE_ROOT/src"
  export SIMPLE_RUNTIME_PATH="$RUNTIME_PATH"
  export SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap
  export SIMPLE_NATIVE_BUILD_TARGET="$STAGE3_RESOLVED_TARGET"
  export SIMPLE_NATIVE_BUILD_CACHE_DIR="$s3h_dir/cache"
  export SIMPLE_FRONTEND_CACHE_DIR="$s3h_dir/cache/frontend"
  export SIMPLE_HIR_CACHE_DIR="$s3h_dir/cache/hir"
  export SIMPLE_CACHE_SCOPE="${s3h_label}-hello"
  export TMPDIR="$s3h_dir/tmp"
  set -- --target "$STAGE3_RESOLVED_TARGET" --backend "$BACKEND" \
    --runtime-bundle core-c-bootstrap --runtime-path "$RUNTIME_PATH" \
    --mode one-binary --threads 1 --cache-dir "$s3h_dir/cache" "$s3h_source" -o "$s3h_out"
  if [ -n "$BACKEND_PLUGIN" ]; then
    set -- "$@" --backend-plugin "$BACKEND_PLUGIN"
  fi
  # run_timeout is inherited by the guarded shell; no exported-function dependency.
  run_guarded_cmd "$s3h_label-hello-compile" "$s3h_dir/compile.log" \
    bash -c '. "$1"; shift; run_timeout 900 "$@"' _ \
    "$SCRIPT_DIR/lib/run-timeout.shs" "$s3h_candidate" native-build "$@" || return $?
  if [ ! -x "$s3h_out" ] || [ "$(wc -c <"$s3h_out" | tr -d ' ')" -le 1024 ]; then
    echo "ERROR: [$s3h_label] Hello artifact missing, non-executable or vacuous" >&2
    return 1
  fi
  sign_stage_outputs "$s3h_dir" "$s3h_out" || return $?
  run_guarded_cmd "$s3h_label-hello-run" "$s3h_dir/stdout" \
    bash -c '. "$1"; shift; run_timeout 30 "$@"' _ \
    "$SCRIPT_DIR/lib/run-timeout.shs" "$s3h_out" || return $?
  cmp "$s3h_dir/expected" "$s3h_dir/stdout" || return $?
)

run_stage3_step() {
  s3_label=$1
  s3_producer=$2
  s3_dir=$3
  s3_out=$4
  s3_scope=$5

  [ -x "$s3_producer" ] || { echo "ERROR: [$s3_label] producer binary missing or not executable: $s3_producer" >&2; exit 2; }
  mkdir -p "$s3_dir/tmp" "$s3_dir/cache/frontend" "$s3_dir/cache/hir" "$s3_dir/hello/cache" "$LOG_DIR"
  rm -rf "$s3_dir/lib"
  rm -f "$s3_out" "${s3_out}.go-to-end.sdn"

  p3_mode_flag="dynload"
  [ "$LINK_MODE" = "one-binary" ] && p3_mode_flag="one-binary"

  s3_log="$LOG_DIR/${s3_scope}.log"
  echo "=== [$s3_label] Building Stage 3 ($COMPILE_MODE mode, link=$LINK_MODE, threads=$THREADS) -> $s3_out ==="

  (
    cd "$SOURCE_ROOT"
    stage3_apply_native_host_link_policy "$STAGE3_RESOLVED_TARGET" "$COMPILE_MODE" "$WIN_CONFIG" "$LINK_MODE"
    apply_windows_toolchain_env
    export TMPDIR="$s3_dir/tmp"
    export SIMPLE_LIB="$SOURCE_ROOT/src"
    export SIMPLE_CACHE_SCOPE="$s3_scope"
    export SIMPLE_FRONTEND_CACHE="1"
    export SIMPLE_FRONTEND_CACHE_DIR="$s3_dir/cache/frontend"
    export SIMPLE_HIR_CACHE="1"
    export SIMPLE_HIR_CACHE_DIR="$s3_dir/cache/hir"
    export SIMPLE_NATIVE_ARENA_DECLS="1"
    export SIMPLE_NO_STUB_FALLBACK="1"
    export SIMPLE_NO_DEPRECATED_WARNINGS="1"
    export SIMPLE_PACKAGE_INDEX_COLD_INIT="1"
    export LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING="1"
    export SIMPLE_NATIVE_BUILD_TARGET="$STAGE3_RESOLVED_TARGET"
    export SIMPLE_NATIVE_BUILD_THREADS="$THREADS"
    export SIMPLE_NATIVE_BUILD_CACHE_DIR="$s3_dir/cache"
    export SIMPLE_RUNTIME_PATH="$RUNTIME_PATH"
    export SIMPLE_NATIVE_RUNTIME_BUNDLE="core-c-bootstrap"
    export SIMPLE_BINARY="$s3_producer"
    # Keep all 6 SIMPLE_STAGE3_* host-match / primitive-archive / dynlib-policy vars exported in BOTH shard and file modes!
    set -- \
      --target "$STAGE3_RESOLVED_TARGET" \
      --backend "$BACKEND" \
      --runtime-bundle core-c-bootstrap \
      --source "$STAGE3_POLICY_K1_ROOT" \
      --source "$STAGE3_POLICY_HOST_COMP_ROOT" \
      --source src/compiler \
      --source src/app \
      --source src/lib
    if [ "${SIMPLE_STAGE3_BUILD_EXTRA_DYNLIBS:-0}" = "1" ]; then
      set -- "$@" --source src/plugins
    fi
    set -- "$@" --entry-closure
    if [ "$COMPILE_MODE" = "shard" ]; then
      set -- "$@" --go-to-end
    fi
    if [ -n "$BACKEND_PLUGIN" ]; then
      set -- "$@" --backend-plugin "$BACKEND_PLUGIN"
    fi
    set -- "$@" \
      --threads "$THREADS" \
      --cache-dir "$s3_dir/cache" \
      --mode "$p3_mode_flag" \
      --runtime-path "$RUNTIME_PATH" \
      --entry src/app/cli/bootstrap_main.spl \
      -o "$s3_out"
    run_guarded_cmd "$s3_label" "$s3_log" "$s3_producer" native-build "$@"
  )

  verify_stage3_dynlibs "$s3_label" "$s3_dir"
  sign_stage_outputs "$s3_dir" "$s3_out"
  "$s3_out" --version | grep -Fq "simple-bootstrap"
  run_stage3_hello "$s3_label" "$s3_out" "$s3_dir" || return $?
  echo "=== [$s3_label] PASS ($s3_out) ==="
}

run_stage4_all() {
  [ -x "$P3B_BIN" ] || { echo "ERROR: [P4] Phase 3b compiler not executable: $P3B_BIN" >&2; exit 2; }
  mkdir -p "$P4_DIR/bin" "$P4_DIR/essentials" "$P4_DIR/cli-release/tmp" "$P4_DIR/cli-release/cache/frontend" "$P4_DIR/cli-release/cache/hir" \
    "$P4_DIR/cli-debug/tmp" "$P4_DIR/cli-debug/cache/frontend" "$P4_DIR/cli-debug/cache/hir" "$P4_DIR/tools-cache/frontend" "$P4_DIR/tools-cache/hir" "$LOG_DIR"

  p4_rel_bin="$P4_DIR/bin/simple${EXE_EXT}"
  p4_dbg_bin="$P4_DIR/bin/simple-debug${EXE_EXT}"

  echo "=== [P4:cli-release] Building Stage 4 Release CLI ($p4_rel_bin) ==="
  (
    cd "$SOURCE_ROOT"
    if unset SIMPLE_BOOTSTRAP_STAGE3 SIMPLE_LINKER 2>/dev/null; then :; fi
    apply_windows_toolchain_env
    export TMPDIR="$P4_DIR/cli-release/tmp"
    export SIMPLE_LIB="$SOURCE_ROOT/src"
    export SIMPLE_BOOTSTRAP="1"
    export SIMPLE_BOOTSTRAP_STAGE4="1"
    export SIMPLE_STAGE4_STREAMING_SURFACES="1"
    export SIMPLE_NATIVE_GO_TO_END="1"
    export SIMPLE_CACHE_SCOPE="stage4"
    export SIMPLE_FRONTEND_CACHE="1"
    export SIMPLE_FRONTEND_CACHE_DIR="$P4_DIR/cli-release/cache/frontend"
    export SIMPLE_HIR_CACHE="1"
    export SIMPLE_HIR_CACHE_DIR="$P4_DIR/cli-release/cache/hir"
    export SIMPLE_NATIVE_ARENA_DECLS="1"
    export SIMPLE_NO_STUB_FALLBACK="1"
    export SIMPLE_NO_DEPRECATED_WARNINGS="1"
    export SIMPLE_PACKAGE_INDEX_COLD_INIT="1"
    export LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING="1"
    export SIMPLE_NATIVE_BUILD_TARGET="$STAGE3_RESOLVED_TARGET"
    export SIMPLE_NATIVE_BUILD_THREADS="$THREADS"
    export SIMPLE_NATIVE_BUILD_CACHE_DIR="$P4_DIR/cli-release/cache"
    export SIMPLE_RUNTIME_PATH="$RUNTIME_PATH"
    export SIMPLE_BINARY="$P3B_BIN"
    if [ "$COMPILE_MODE" = "shard" ]; then
      export SIMPLE_FILE_WORKERS="0"
      export SIMPLE_HIR_SHARDING="1"
      export SIMPLE_MIR_SHARDING="1"
    else
      export SIMPLE_FILE_WORKERS="1"
      if unset SIMPLE_HIR_SHARDING SIMPLE_MIR_SHARDING 2>/dev/null; then :; fi
    fi

    set -- \
      --target "$STAGE3_RESOLVED_TARGET" \
      --backend "$BACKEND" \
      --runtime-bundle core-c-bootstrap \
      --source src/compositions/cuda_disabled \
      --source src/compiler \
      --source src/app \
      --source src/lib \
      --source src/os \
      --source src/plugins \
      --entry-closure
    if [ -n "$BACKEND_PLUGIN" ]; then
      set -- "$@" --backend-plugin "$BACKEND_PLUGIN"
    fi
    set -- "$@" \
      --timeout 14400 \
      --profile=prod --release --strip \
      --threads "$THREADS" \
      --cache-dir "$P4_DIR/cli-release/cache" \
      --mode "$P4_LINK_MODE" \
      --entry src/app/cli/main.spl \
      --runtime-path "$RUNTIME_PATH" \
      -o "$p4_rel_bin"
    run_guarded_cmd "P4-cli-release" "$LOG_DIR/p4-cli-release.log" "$P3B_BIN" native-build "$@"
  )
  sign_stage_outputs "$P4_DIR/bin" "$p4_rel_bin"

  echo "=== [P4:cli-debug-xray] Building Stage 4 Debug + XRay CLI ($p4_dbg_bin) ==="
  (
    cd "$SOURCE_ROOT"
    if unset SIMPLE_BOOTSTRAP_STAGE3 SIMPLE_LINKER 2>/dev/null; then :; fi
    apply_windows_toolchain_env
    export TMPDIR="$P4_DIR/cli-debug/tmp"
    export SIMPLE_LIB="$SOURCE_ROOT/src"
    export SIMPLE_BOOTSTRAP="1"
    export SIMPLE_BOOTSTRAP_STAGE4="1"
    export SIMPLE_STAGE4_STREAMING_SURFACES="1"
    export SIMPLE_NATIVE_GO_TO_END="1"
    export SIMPLE_CACHE_SCOPE="stage4-debug"
    export SIMPLE_FRONTEND_CACHE="1"
    export SIMPLE_FRONTEND_CACHE_DIR="$P4_DIR/cli-debug/cache/frontend"
    export SIMPLE_HIR_CACHE="1"
    export SIMPLE_HIR_CACHE_DIR="$P4_DIR/cli-debug/cache/hir"
    export SIMPLE_NATIVE_ARENA_DECLS="1"
    export SIMPLE_NO_STUB_FALLBACK="1"
    export SIMPLE_NO_DEPRECATED_WARNINGS="1"
    export SIMPLE_PACKAGE_INDEX_COLD_INIT="1"
    export LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING="1"
    export SIMPLE_NATIVE_BUILD_TARGET="$STAGE3_RESOLVED_TARGET"
    export SIMPLE_NATIVE_BUILD_THREADS="$THREADS"
    export SIMPLE_NATIVE_BUILD_CACHE_DIR="$P4_DIR/cli-debug/cache"
    export SIMPLE_RUNTIME_PATH="$RUNTIME_PATH"
    export SIMPLE_BINARY="$P3B_BIN"
    if [ "$COMPILE_MODE" = "shard" ]; then
      export SIMPLE_FILE_WORKERS="0"
      export SIMPLE_HIR_SHARDING="1"
      export SIMPLE_MIR_SHARDING="1"
    else
      export SIMPLE_FILE_WORKERS="1"
      if unset SIMPLE_HIR_SHARDING SIMPLE_MIR_SHARDING 2>/dev/null; then :; fi
    fi

    set -- \
      --target "$STAGE3_RESOLVED_TARGET" \
      --backend "$BACKEND" \
      --runtime-bundle core-c-bootstrap \
      --source src/compositions/cuda_disabled \
      --source src/compiler \
      --source src/app \
      --source src/lib \
      --source src/os \
      --source src/plugins \
      --entry-closure
    if [ -n "$BACKEND_PLUGIN" ]; then
      set -- "$@" --backend-plugin "$BACKEND_PLUGIN"
    fi
    set -- "$@" \
      --timeout 14400 \
      --profile=dev --debug --no-strip --xray \
      --threads "$THREADS" \
      --cache-dir "$P4_DIR/cli-debug/cache" \
      --mode "$P4_LINK_MODE" \
      --entry src/app/cli/main.spl \
      --runtime-path "$RUNTIME_PATH" \
      -o "$p4_dbg_bin"
    run_guarded_cmd "P4-cli-debug-xray" "$LOG_DIR/p4-cli-debug-xray.log" "$P3B_BIN" native-build "$@"
  )
  sign_stage_outputs "$P4_DIR/bin" "$p4_dbg_bin"

  for tool_spec in \
    "simple_test_runner:src/app/test_runner_new/main.spl" \
    "simple_build_runner:src/app/buildrunner/main.spl" \
    "simple_mcp_server:src/app/mcp/main.spl" \
    "simple_lsp_mcp_server:src/app/simple_lsp_mcp/main.spl"; do
    t_name="${tool_spec%%:*}"
    t_entry="${tool_spec#*:}"
    t_out="$P4_DIR/essentials/${t_name}${EXE_EXT}"
    mkdir -p "$P4_DIR/$t_name/tmp"
    echo "=== [P4:$t_name] Building Stage 5 tool ($t_out) ==="
    (
      cd "$SOURCE_ROOT"
      if unset SIMPLE_BOOTSTRAP SIMPLE_BOOTSTRAP_STAGE3 SIMPLE_BOOTSTRAP_STAGE4 SIMPLE_LINKER 2>/dev/null; then :; fi
      apply_windows_toolchain_env
      export TMPDIR="$P4_DIR/$t_name/tmp"
      export SIMPLE_LIB="$SOURCE_ROOT/src"
      export SIMPLE_CACHE_SCOPE="stage5-tools"
      export SIMPLE_FRONTEND_CACHE="1"
      export SIMPLE_FRONTEND_CACHE_DIR="$P4_DIR/tools-cache/frontend"
      export SIMPLE_HIR_CACHE="1"
      export SIMPLE_HIR_CACHE_DIR="$P4_DIR/tools-cache/hir"
      export SIMPLE_NATIVE_ARENA_DECLS="1"
      export SIMPLE_NO_STUB_FALLBACK="1"
      export SIMPLE_NO_DEPRECATED_WARNINGS="1"
      export SIMPLE_PACKAGE_INDEX_COLD_INIT="1"
      export LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING="1"
      export SIMPLE_RUNTIME_PATH="$RUNTIME_PATH"
      export SIMPLE_BINARY="$P3B_BIN"
      set -- \
        --target "$STAGE3_RESOLVED_TARGET" \
        --backend "$BACKEND" \
        --runtime-bundle core-c-bootstrap \
        --source src/compositions/cuda_disabled \
        --source src/compiler \
        --source src/app \
        --source src/lib \
        --source src/plugins \
        --entry-closure
      if [ -n "$BACKEND_PLUGIN" ]; then
        set -- "$@" --backend-plugin "$BACKEND_PLUGIN"
      fi
      set -- "$@" \
        --threads "$THREADS" \
        --cache-dir "$P4_DIR/tools-cache" \
        --mode one-binary \
        --entry "$t_entry" \
        --runtime-path "$RUNTIME_PATH" \
        --timeout 14400 \
        -o "$t_out"
      run_guarded_cmd "P4-$t_name" "$LOG_DIR/p4-${t_name}.log" "$P3B_BIN" native-build "$@"
    )
    sign_stage_outputs "$P4_DIR/essentials" "$t_out"
  done
  echo "=== [P4] PASS ==="
}

case "$PHASE" in
  p3a)
    run_stage3_step "P3a" "$P2_BIN" "$P3A_DIR" "$P3A_BIN" "stage3-a"
    ;;
  p3b)
    # This is the same P3b operation used by p3/all, without rebuilding P3a.
    # A fresh root prevents cleanup/cache writes from touching the prior product.
    [ ! -e "$BUILD_ROOT" ] && [ ! -L "$BUILD_ROOT" ] || { echo 'ERROR: standalone P3b requires a fresh build root' >&2; exit 2; }
    [ -x "$P3A_BIN" ] || { echo 'ERROR: standalone P3b requires an executable P3a' >&2; exit 2; }
    . "$SCRIPT_DIR/../check/lib/bootstrap-stage3/authority.shs"
    [ "$(bootstrap_stage3_hash_file "$P3A_BIN")" = "$P3A_SHA256" ] || { echo 'ERROR: P3a digest mismatch before build' >&2; exit 2; }
    # An explicit output outside the fresh root could overwrite the producer.
    [ "$P3B_BIN" = "$P3B_DIR/simple${EXE_EXT}" ] || { echo 'ERROR: standalone P3b output must remain in its fresh build root' >&2; exit 2; }
    if [ -n "$P3B_CACHE_FROM" ]; then
      [ -d "$P3B_CACHE_FROM" ] || { echo 'ERROR: P3b cache source must be a directory' >&2; exit 2; }
      p3b_cache_source=$(realpath -- "$P3B_CACHE_FROM") || exit 2
      p3b_build_root=$(realpath -m -- "$BUILD_ROOT") || exit 2
      case "$p3b_build_root/" in
        "${p3b_cache_source%/}/"*) echo 'ERROR: P3b build root must be outside the source cache' >&2; exit 2 ;;
      esac
      p3b_special=$(find "$p3b_cache_source" ! -type f ! -type d -print -quit) || exit 2
      [ -z "$p3b_special" ] || { echo 'ERROR: P3b cache must contain only regular files and directories' >&2; exit 2; }
      mkdir -p "$(dirname -- "$BUILD_ROOT")"
      mkdir -- "$BUILD_ROOT"
      mkdir -p "$P3B_DIR/cache"
      cp -a --reflink=auto "$p3b_cache_source/." "$P3B_DIR/cache/"
    fi
    run_stage3_step "P3b" "$P3A_BIN" "$P3B_DIR" "$P3B_BIN" "stage3-b"
    [ "$(bootstrap_stage3_hash_file "$P3A_BIN")" = "$P3A_SHA256" ] || { echo 'ERROR: P3a changed during build' >&2; exit 2; }
    ;;
  p3)
    run_stage3_step "P3a" "$P2_BIN" "$P3A_DIR" "$P3A_BIN" "stage3-a"
    run_stage3_step "P3b" "$P3A_BIN" "$P3B_DIR" "$P3B_BIN" "stage3-b"
    ;;
  p4)
    # An externally supplied P3b has not passed this invocation's Hello gate.
    run_stage3_hello "P4-producer" "$P3B_BIN" "$P4_DIR/producer" || exit $?
    run_stage4_all
    ;;
  all)
    run_stage3_step "P3a" "$P2_BIN" "$P3A_DIR" "$P3A_BIN" "stage3-a"
    run_stage3_step "P3b" "$P3A_BIN" "$P3B_DIR" "$P3B_BIN" "stage3-b"
    run_stage4_all
    ;;
esac
