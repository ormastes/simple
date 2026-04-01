#!/usr/bin/env bash
set -euo pipefail

# Windows bootstrap script for Simple compiler (MSVC or MinGW).
#
# Runs in MSYS2/Git Bash. Detects MSVC vs MinGW environment and
# configures CC/CXX accordingly for the native-build linker.
#
# Output layout uses <arch>-<vendor>-<os>-<abi> target triple:
#   build/bootstrap/stage1/<triple>/simple.exe
#   build/bootstrap/stage2/<triple>/simple.exe
#   build/bootstrap/stage3/<triple>/simple.exe
#
# Triple format: <arch>-<vendor>-<os>-<abi>
#   MSVC:  x86_64-pc-windows-msvc
#   MinGW: x86_64-pc-windows-gnu
#
# Usage:
#   scripts/bootstrap/bootstrap-windows.sh [options]
#
# Options:
#   --backend=<name>   Backend for stage2/stage3 (default: llvm-lib)
#   --output=<dir>     Output directory (default: build/bootstrap)
#   --deploy           Compile full CLI and deploy to bin/release/<triple>/simple.exe
#   --msvc             Force MSVC toolchain
#   --mingw            Force MinGW toolchain
#   --help             Show this help

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/bootstrap-windows.sh [options]

Windows bootstrap wrapper for the verified staged bootstrap pipeline.
Detects MSVC vs MinGW environment automatically.

Output: <output>/stage{1,2,3}/<arch>-<vendor>-<os>-<abi>/simple.exe

Options:
  --backend=<name>   Backend for stage2/stage3 (default: llvm-lib)
  --output=<dir>     Output directory (default: build/bootstrap)
  --deploy           Compile full CLI and deploy to bin/release/<triple>/simple.exe
  --msvc             Force MSVC toolchain
  --mingw            Force MinGW toolchain
  --help             Show this help
EOF
}

backend=""
output_dir="build/bootstrap"
deploy=0
force_toolchain=""

while (($#)); do
  case "$1" in
    --backend=*) backend="${1#*=}" ;;
    --output=*)  output_dir="${1#*=}" ;;
    --deploy)    deploy=1 ;;
    --msvc)      force_toolchain="msvc" ;;
    --mingw)     force_toolchain="mingw" ;;
    --help|-h)   usage; exit 0 ;;
    *)           echo "error: unknown option '$1'" >&2; usage >&2; exit 1 ;;
  esac
  shift
done

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
cd "${repo_root}"

# ===========================================================================
# Platform detection — <arch>-<vendor>-<os>-<abi> target triple
# ===========================================================================

FORCE_TOOLCHAIN="${force_toolchain}"
export FORCE_TOOLCHAIN
. "${repo_root}/scripts/platform-detect.sh"

PLATFORM="${PLATFORM_TRIPLE}"
arch="${PLATFORM_ARCH}"
toolchain="${PLATFORM_ABI}"  # msvc or gnu
if [[ "$toolchain" == "gnu" ]]; then
  toolchain="mingw"
fi

echo "Platform: ${PLATFORM}"
echo "  arch:      ${PLATFORM_ARCH}"
echo "  vendor:    ${PLATFORM_VENDOR}"
echo "  os:        ${PLATFORM_OS}"
echo "  abi:       ${PLATFORM_ABI}"
echo "  toolchain: ${toolchain}"

log_dir="${output_dir}/logs/${PLATFORM}"
mkdir -p "${log_dir}"

run_logged() {
  local label="$1"
  shift
  local log_file="${log_dir}/${label}.log"
  {
    echo "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] ${label}"
    echo "cwd: $(pwd)"
    echo "command: $*"
    echo ""
  } >"${log_file}"

  set +e
  "$@" >>"${log_file}" 2>&1
  local status=$?
  # MSYS2 can fail to execute large PE files (exit 126 "Exec format error").
  # Retry via cmd.exe with Windows paths as a workaround.
  if [[ "${status}" -eq 126 ]]; then
    echo "  (retrying via cmd.exe — MSYS2 exec format workaround)"
    local win_args=()
    for a in "$@"; do
      if [[ -f "$a" ]]; then
        win_args+=("$(cygpath -w "$a")")
      else
        win_args+=("$a")
      fi
    done
    cmd.exe //c "${win_args[@]}" >>"${log_file}" 2>&1
    status=$?
  fi
  set -e

  echo "  ${label} log: ${log_file}"
  if [[ "${status}" -ne 0 ]]; then
    echo "error: ${label} failed with exit ${status}" >&2
    if [[ "${status}" -ge 128 ]]; then
      echo "error: ${label} terminated by signal $((status - 128))" >&2
    fi
    echo "error: see log ${log_file}" >&2
    exit "${status}"
  fi
}

# ===========================================================================
# Compiler configuration
# ===========================================================================

if [[ "$toolchain" == "msvc" ]]; then
  for cc_candidate in clang-cl clang; do
    if command -v "$cc_candidate" &>/dev/null && "$cc_candidate" --version &>/dev/null 2>&1; then
      export CC="$cc_candidate"
      break
    fi
  done
  for cxx_candidate in clang++ g++; do
    if command -v "$cxx_candidate" &>/dev/null && "$cxx_candidate" --version &>/dev/null 2>&1; then
      export CXX="$cxx_candidate"
      break
    fi
  done
  echo "MSVC mode: CC=${CC:-auto} CXX=${CXX:-auto}"
else
  export CC="${CC:-gcc}"
  export CXX="${CXX:-g++}"
  echo "MinGW mode: CC=${CC} CXX=${CXX}"
fi

# Build Rust seed if needed
seed_bin="src/compiler_rust/target/bootstrap/simple.exe"
if [[ ! -f "${seed_bin}" ]]; then
  echo "Building Rust seed compiler..."
  run_logged rust-seed-build cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver
fi

backend_flag=()
if [[ -n "${backend}" ]]; then
  backend_flag=(--backend "${backend}")
fi

echo ""
echo "Running Windows bootstrap pipeline..."
echo "  platform:   ${PLATFORM}"
echo "  backend:    ${backend:-default}"
echo "  output:     ${output_dir}"
echo ""

# ===========================================================================
# Three-stage bootstrap — output to stage{N}/<arch>-<os>-<abi>/simple.exe
# ===========================================================================

stage1_dir="${output_dir}/stage1/${PLATFORM}"
stage2_dir="${output_dir}/stage2/${PLATFORM}"
stage3_dir="${output_dir}/stage3/${PLATFORM}"
mkdir -p "${stage1_dir}" "${stage2_dir}" "${stage3_dir}"

stage1_bin="${stage1_dir}/simple.exe"
stage2_bin="${stage2_dir}/simple.exe"
stage3_bin="${stage3_dir}/simple.exe"

export RUST_LOG="${RUST_LOG:-error}"

# Stage 1: Rust seed → stage1
echo "=== Stage 1: Rust seed → stage1 ==="
run_logged stage1-native-build \
  "${seed_bin}" native-build \
    --source src/compiler --source src/lib --source src/app \
    --entry-closure \
    --entry src/app/cli/bootstrap_main.spl \
    "${backend_flag[@]}" \
    -o "${stage1_bin}" \
    --clean

if [[ ! -f "${stage1_bin}" ]]; then
  echo "error: stage1 binary not produced" >&2
  exit 1
fi

echo "Stage 1 complete: ${stage1_bin}"

# Stage 2: stage1 → stage2
echo ""
echo "=== Stage 2: stage1 → stage2 (${backend:-default}) ==="
run_logged stage2-native-build "${stage1_bin}" native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry-closure \
  --entry src/app/cli/bootstrap_main.spl \
  "${backend_flag[@]}" \
  -o "${stage2_bin}" \
  --clean

if [[ ! -f "${stage2_bin}" ]]; then
  echo "error: stage2 binary not produced" >&2
  exit 1
fi

echo "Stage 2 complete: ${stage2_bin}"

# Stage 3: stage2 → stage3 (verify)
echo ""
echo "=== Stage 3: stage2 → stage3 (${backend:-default}, verify) ==="
run_logged stage3-native-build "${stage2_bin}" native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry-closure \
  --entry src/app/cli/bootstrap_main.spl \
  "${backend_flag[@]}" \
  -o "${stage3_bin}" \
  --clean

if [[ ! -f "${stage3_bin}" ]]; then
  echo "error: stage3 binary not produced" >&2
  exit 1
fi

echo "Stage 3 complete: ${stage3_bin}"

# Verify stage2 == stage3
hash2="$(sha256sum "${stage2_bin}" | awk '{print $1}')"
hash3="$(sha256sum "${stage3_bin}" | awk '{print $1}')"

echo ""
echo "stage2 sha256: ${hash2}"
echo "stage3 sha256: ${hash3}"

if [[ "${hash2}" != "${hash3}" ]]; then
  echo "error: stage2 and stage3 hashes differ" >&2
  exit 1
fi

echo ""
echo "Bootstrap verification passed."

# ===========================================================================
# Stage 4: Compile full CLI (main.spl) with verified bootstrap compiler
# ===========================================================================

echo ""
echo "=== Stage 4: compiling full CLI (main.spl) with verified bootstrap compiler ==="
full_dir="${output_dir}/full/${PLATFORM}"
mkdir -p "${full_dir}"
full_bin="${full_dir}/simple.exe"

run_logged stage4-native-build "${stage3_bin}" native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry-closure \
  --entry src/app/cli/main.spl \
  "${backend_flag[@]}" \
  -o "${full_bin}" \
  --clean

if [[ ! -f "${full_bin}" ]]; then
  echo "error: failed to compile full CLI binary from main.spl" >&2
  exit 1
fi

echo "Full CLI binary: ${full_bin}"

if (( deploy )); then
  # Deploy to triple-specific directory
  deploy_dir="bin/release/${PLATFORM}"
  mkdir -p "${deploy_dir}"
  cp "${full_bin}" "${deploy_dir}/simple.exe"
  echo "Deployed full CLI binary to ${deploy_dir}/simple.exe"

  # Recreate symlinks
  cmd.exe /c "${repo_root}\\scripts\\setup.cmd" || true
fi

echo ""
echo "Final binary: ${full_bin}"
