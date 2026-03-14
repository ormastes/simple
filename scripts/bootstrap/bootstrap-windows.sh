#!/usr/bin/env bash
set -euo pipefail

# Windows bootstrap script for Simple compiler (MSVC or MinGW).
#
# Runs in MSYS2/Git Bash. Detects MSVC vs MinGW environment and
# configures CC/CXX accordingly for the native-build linker.
#
# Usage:
#   scripts/bootstrap/bootstrap-windows.sh [options]
#
# Options:
#   --backend=<name>   Backend for stage2/stage3 (default: llvm-lib)
#   --output=<dir>     Output directory (default: bootstrap)
#   --deploy           Copy verified stage3 to bin/release/simple.exe
#   --msvc             Force MSVC toolchain
#   --mingw            Force MinGW toolchain
#   --help             Show this help

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/bootstrap-windows.sh [options]

Windows bootstrap wrapper for the verified staged bootstrap pipeline.
Detects MSVC vs MinGW environment automatically.

Options:
  --backend=<name>   Backend for stage2/stage3 (default: llvm-lib)
  --output=<dir>     Output directory (default: bootstrap)
  --deploy           Copy verified stage3 to bin/release/simple.exe
  --msvc             Force MSVC toolchain
  --mingw            Force MinGW toolchain
  --help             Show this help
EOF
}

backend="llvm-lib"
output_dir="bootstrap"
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

# Detect toolchain
detect_toolchain() {
  if [[ -n "$force_toolchain" ]]; then
    echo "$force_toolchain"
    return
  fi
  # Check for MSYSTEM env var (MSYS2)
  if [[ "${MSYSTEM:-}" == MINGW* ]]; then
    echo "mingw"
  elif command -v cl.exe &>/dev/null; then
    echo "msvc"
  elif command -v clang-cl &>/dev/null && clang-cl --version &>/dev/null; then
    echo "msvc"
  elif command -v gcc &>/dev/null; then
    echo "mingw"
  else
    echo "msvc"  # default
  fi
}

toolchain="$(detect_toolchain)"
echo "Detected toolchain: ${toolchain}"

# Configure CC/CXX based on toolchain
if [[ "$toolchain" == "msvc" ]]; then
  # Find working MSVC-targeting clang
  for cc_candidate in clang-cl clang; do
    if command -v "$cc_candidate" &>/dev/null && "$cc_candidate" --version &>/dev/null 2>&1; then
      export CC="$cc_candidate"
      break
    fi
  done
  # Find clang++ that targets MSVC
  for cxx_candidate in clang++ g++; do
    if command -v "$cxx_candidate" &>/dev/null && "$cxx_candidate" --version &>/dev/null 2>&1; then
      export CXX="$cxx_candidate"
      break
    fi
  done
  echo "MSVC mode: CC=${CC:-auto} CXX=${CXX:-auto}"
else
  # MinGW: prefer gcc/g++
  export CC="${CC:-gcc}"
  export CXX="${CXX:-g++}"
  echo "MinGW mode: CC=${CC} CXX=${CXX}"
fi

# Build Rust seed if needed
seed_bin="src/compiler_rust/target/bootstrap/simple.exe"
if [[ ! -f "${seed_bin}" ]]; then
  echo "Building Rust seed compiler..."
  cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver
fi

echo ""
echo "Running Windows bootstrap pipeline..."
echo "  backend:    ${backend}"
echo "  output:     ${output_dir}"
echo "  toolchain:  ${toolchain}"
echo ""

mkdir -p "${output_dir}"

# Stage 1: Rust seed → stage1
echo "=== Stage 1: Rust seed → stage1 ==="
RUST_LOG="${RUST_LOG:-error}" \
  "${seed_bin}" native-build \
    --source src/compiler --source src/lib --source src/app \
    --entry src/app/cli/main.spl \
    -o "${output_dir}/simple_stage1.exe" \
    --clean

if [[ ! -f "${output_dir}/simple_stage1.exe" ]]; then
  echo "error: stage1 binary not produced" >&2
  exit 1
fi

echo "Stage 1 complete: ${output_dir}/simple_stage1.exe"

# Stage 2: stage1 → stage2 (with llvm-lib backend)
echo ""
echo "=== Stage 2: stage1 → stage2 (${backend}) ==="
"${output_dir}/simple_stage1.exe" native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry src/app/cli/main.spl \
  --backend "${backend}" \
  -o "${output_dir}/simple_stage2.exe" \
  --clean

if [[ ! -f "${output_dir}/simple_stage2.exe" ]]; then
  echo "error: stage2 binary not produced" >&2
  exit 1
fi

echo "Stage 2 complete: ${output_dir}/simple_stage2.exe"

# Stage 3: stage2 → stage3 (verify)
echo ""
echo "=== Stage 3: stage2 → stage3 (${backend}, verify) ==="
"${output_dir}/simple_stage2.exe" native-build \
  --source src/compiler --source src/lib --source src/app \
  --entry src/app/cli/main.spl \
  --backend "${backend}" \
  -o "${output_dir}/simple_stage3.exe" \
  --clean

if [[ ! -f "${output_dir}/simple_stage3.exe" ]]; then
  echo "error: stage3 binary not produced" >&2
  exit 1
fi

echo "Stage 3 complete: ${output_dir}/simple_stage3.exe"

# Verify stage2 == stage3
hash2="$(sha256sum "${output_dir}/simple_stage2.exe" | awk '{print $1}')"
hash3="$(sha256sum "${output_dir}/simple_stage3.exe" | awk '{print $1}')"

echo ""
echo "stage2 sha256: ${hash2}"
echo "stage3 sha256: ${hash3}"

if [[ "${hash2}" != "${hash3}" ]]; then
  echo "error: stage2 and stage3 hashes differ" >&2
  exit 1
fi

if (( deploy )); then
  mkdir -p bin/release
  cp "${output_dir}/simple_stage3.exe" "bin/release/simple.exe"
  echo "Deployed verified binary to bin/release/simple.exe"

  # Create bin/simple.cmd wrapper (Windows equivalent of bin/simple -> release/simple symlink)
  cat > bin/simple.cmd <<'WRAPPER'
@echo off
"%~dp0release\simple.exe" %*
WRAPPER
  echo "Created bin/simple.cmd wrapper (forwards to bin/release/simple.exe)"
fi

echo ""
echo "Bootstrap verification passed."
echo "Final binary: ${output_dir}/simple_stage3.exe"
