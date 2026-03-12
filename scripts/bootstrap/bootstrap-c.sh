#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/bootstrap-c.sh [options]

Build the temporal C bootstrap binary for Linux using the generated C backend.

Status:
  Experimental in this checkout. The staged llvm-lib bootstrap is the
  canonical Linux path. This script is useful for C backend debugging and
  temporal bootstrap work.

Options:
  --verify        Run the produced bootstrap binary with --version
  --help          Show this help
EOF
}

verify=0

while (($#)); do
  case "$1" in
    --verify)
      verify=1
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown option '$1'" >&2
      usage >&2
      exit 1
      ;;
  esac
  shift
done

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
cd "${repo_root}"

codegen_bin="build/simple_codegen"
if [[ ! -x "${codegen_bin}" ]]; then
  codegen_bin="bin/bootstrap/cpp/simple_codegen"
fi

if [[ ! -x "${codegen_bin}" ]]; then
  echo "error: simple_codegen not found at build/simple_codegen or bin/bootstrap/cpp/simple_codegen" >&2
  exit 1
fi

cc_bin="${CC:-clang}"
cmake_generator="${CMAKE_GENERATOR:-Ninja}"
log_file="build/bootstrap/c_simple/bootstrap-c.log"

mkdir -p build/bootstrap/c_simple

echo "Generating C bootstrap source..."
"${codegen_bin}" src/app/cli/main.spl src/compiler_cpp/main.c

echo "Configuring C bootstrap build..."
cmake -B build -G "${cmake_generator}" -DCMAKE_C_COMPILER="${cc_bin}" -S src/compiler_cpp >"${log_file}" 2>&1

echo "Building C bootstrap..."
if ! cmake --build build >>"${log_file}" 2>&1; then
  echo "error: C bootstrap build failed" >&2
  echo "log: ${log_file}" >&2
  tail -n 40 "${log_file}" >&2 || true
  exit 1
fi

install -Dm755 build/simple build/bootstrap/c_simple/simple
install -Dm755 build/simple bin/bootstrap/cpp/simple
if [[ -x build/simple_codegen ]]; then
  install -Dm755 build/simple_codegen build/bootstrap/c_simple/simple_codegen
  install -Dm755 build/simple_codegen bin/bootstrap/cpp/simple_codegen
fi

if (( verify )); then
  echo "Verifying C bootstrap binary..."
  build/bootstrap/c_simple/simple --version
fi

echo "C bootstrap ready at build/bootstrap/c_simple/simple"
