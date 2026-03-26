#!/bin/sh
set -eu

# Bootstrap wrapper for Linux and FreeBSD.
#
# Output layout uses <arch>-<vendor>-<os>-<abi> target triple:
#   build/bootstrap/stage{1,2,3}/<triple>/simple
#
# Triple examples:
#   Linux:   x86_64-unknown-linux-gnu
#   FreeBSD: x86_64-unknown-freebsd-elf

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/bootstrap-from-scratch.sh [options]

Bootstrap wrapper.

Linux:
  Runs the verified staged bootstrap pipeline using bin/release/simple.

FreeBSD / --target=freebsd-x86_64:
  Runs the FreeBSD seed bootstrap verifier using bin/freebsd/simple.

Output: <output>/stage{1,2,3}/<arch>-<vendor>-<os>-<abi>/simple

Options:
  --backend=<name>   Backend for Linux stage2/stage3 (default: llvm-lib)
  --output=<dir>     Output directory for bootstrap artifacts (default: build/bootstrap)
  --deploy           Copy the resulting/compiler artifact into bin/simple when supported
  --target=<triple>  Target platform (freebsd-x86_64 dispatches to FreeBSD flow)
  --verbose          Accepted for compatibility
  --jobs=<n>         Accepted for compatibility
  --keep-artifacts   Accepted for compatibility; artifacts are kept
  --no-verify        Accepted for compatibility; hash verification still runs
  --help             Show this help
EOF
}

backend="llvm-lib"
output_dir="build/bootstrap"
deploy=0
target=""
verbose=0
jobs=""

while [ "$#" -gt 0 ]; do
  case "$1" in
    --backend=*)
      backend=${1#*=}
      ;;
    --output=*)
      output_dir=${1#*=}
      ;;
    --target=*)
      target=${1#*=}
      ;;
    --jobs=*)
      jobs=${1#*=}
      ;;
    --deploy)
      deploy=1
      ;;
    --verbose)
      verbose=1
      ;;
    --keep-artifacts|--no-verify)
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

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "${script_dir}/../.." && pwd)
cd "${repo_root}"

# ===========================================================================
# Platform detection — <arch>-<vendor>-<os>-<abi> target triple
# ===========================================================================

host_os=$(uname -s 2>/dev/null || echo unknown)

# FreeBSD dispatch (separate script)
if [ "${target}" = "freebsd-x86_64" ] || [ "${host_os}" = "FreeBSD" ]; then
  freebsd_args="--output=${output_dir}"
  if [ "${deploy}" -eq 1 ]; then
    freebsd_args="${freebsd_args} --deploy"
  fi
  if [ "${verbose}" -eq 1 ]; then
    freebsd_args="${freebsd_args} --verbose"
  fi
  if [ -n "${jobs}" ]; then
    freebsd_args="${freebsd_args} --jobs=${jobs}"
  fi
  exec "${repo_root}/scripts/bootstrap/bootstrap-freebsd-seed.sh" ${freebsd_args}
fi

# Detect arch
arch=$(uname -m 2>/dev/null || echo x86_64)
case "${arch}" in
  x86_64|amd64)  arch="x86_64" ;;
  aarch64|arm64) arch="aarch64" ;;
  i686|i386)     arch="i686" ;;
esac

# Build target triple
vendor="unknown"
case "${host_os}" in
  Linux)
    os="linux"
    abi="gnu"
    ;;
  Darwin)
    os="darwin"
    vendor="apple"
    abi="macho"
    ;;
  FreeBSD)
    os="freebsd"
    abi="elf"
    ;;
  *)
    os=$(echo "${host_os}" | tr '[:upper:]' '[:lower:]')
    abi="elf"
    ;;
esac

PLATFORM="${arch}-${vendor}-${os}-${abi}"
echo "Platform: ${PLATFORM}"

# ===========================================================================
# Bootstrap pipeline
# ===========================================================================

seed_bin="src/compiler_rust/target/bootstrap/simple"

if [ ! -x "${seed_bin}" ]; then
  echo "Building Rust seed compiler..."
  cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver
fi

# Detect whether bin/release/simple is a full CLI or bootstrap-only
can_full_bootstrap=0
if [ -x "bin/release/simple" ]; then
  # Full CLI supports "build"; bootstrap-only does not
  if bin/release/simple build --help >/dev/null 2>&1; then
    can_full_bootstrap=1
  fi
fi

export SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap"
echo "Running bootstrap pipeline..."
echo "  runtime:  ${SIMPLE_RUNTIME_PATH}"
echo "  platform: ${PLATFORM}"
echo "  backend:  ${backend}"
echo "  output:   ${output_dir}"

if [ "${can_full_bootstrap}" -eq 1 ]; then
  # Full CLI available — use high-level staged bootstrap
  echo "  mode:     full CLI (build bootstrap)"
  RUST_LOG="${RUST_LOG:-error}" \
    SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap" \
    bin/release/simple build bootstrap "--backend=${backend}" "--output=${output_dir}"
else
  # Bootstrap-only or missing — manual staged bootstrap via seed
  echo "  mode:     manual (seed → bootstrap_main → bootstrap_main)"
  if [ ! -x "${seed_bin}" ]; then
    echo "error: Rust seed required for manual bootstrap (${seed_bin})" >&2
    echo "Run: cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver" >&2
    exit 1
  fi

  # Stage 2: seed compiles bootstrap_main.spl
  mkdir -p "${output_dir}/stage2/${PLATFORM}"
  echo "Stage 2: seed → bootstrap_main.spl"
  rm -rf .simple/native_cache/
  SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap" \
  "${seed_bin}" native-build \
    --entry src/app/cli/bootstrap_main.spl \
    -o "${output_dir}/stage2/${PLATFORM}/simple"

  # Stage 3: stage2 recompiles bootstrap_main.spl (self-host verification)
  mkdir -p "${output_dir}/stage3/${PLATFORM}"
  echo "Stage 3: stage2 → bootstrap_main.spl (self-host)"
  rm -rf .simple/native_cache/
  SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap" \
  "${output_dir}/stage2/${PLATFORM}/simple" native-build \
    --entry src/app/cli/bootstrap_main.spl \
    -o "${output_dir}/stage3/${PLATFORM}/simple"
fi

# Locate stage outputs — check new layout first, fall back to flat
if [ -x "${output_dir}/stage2/${PLATFORM}/simple" ]; then
  stage2="${output_dir}/stage2/${PLATFORM}/simple"
  stage3="${output_dir}/stage3/${PLATFORM}/simple"
elif [ -x "${output_dir}/simple_stage2" ]; then
  stage2="${output_dir}/simple_stage2"
  stage3="${output_dir}/simple_stage3"
else
  echo "error: expected bootstrap artifacts were not produced" >&2
  exit 1
fi

if [ ! -x "${stage2}" ] || [ ! -x "${stage3}" ]; then
  echo "error: expected bootstrap artifacts were not produced" >&2
  exit 1
fi

hash2=$(sha256sum "${stage2}" | awk '{print $1}')
hash3=$(sha256sum "${stage3}" | awk '{print $1}')

echo "stage2 sha256: ${hash2}"
echo "stage3 sha256: ${hash3}"

if [ "${hash2}" != "${hash3}" ]; then
  echo "error: stage2 and stage3 hashes differ" >&2
  exit 1
fi

echo "Bootstrap verification passed."

# ===========================================================================
# Stage 4: Compile full CLI (main.spl) with verified bootstrap compiler
# ===========================================================================

echo "Stage 4: compiling full CLI (main.spl) with verified bootstrap compiler..."
full_dir="${output_dir}/full/${PLATFORM}"
mkdir -p "${full_dir}"
rm -rf .simple/native_cache/
SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap" \
"${stage3}" native-build \
  --entry src/app/cli/main.spl \
  -o "${full_dir}/simple"

full_bin="${full_dir}/simple"
if [ ! -x "${full_bin}" ]; then
  echo "error: failed to compile full CLI binary from main.spl" >&2
  exit 1
fi

echo "Full CLI binary: ${full_bin}"

# ===========================================================================
# Deploy
# ===========================================================================

if [ "${deploy}" -eq 1 ]; then
  # Resolve deploy directory — prefer existing legacy format (os-arch), else use triple
  if [ -d "bin/release/${os}-${arch}" ]; then
    deploy_dir="bin/release/${os}-${arch}"
  else
    deploy_dir="bin/release/${PLATFORM}"
  fi
  mkdir -p "${deploy_dir}"
  install -m755 "${full_bin}" "${deploy_dir}/simple"
  echo "Deployed full CLI binary to ${deploy_dir}/simple"

  # Recreate symlinks (bin/simple → release/<platform>/simple)
  "${repo_root}/scripts/setup.sh"
fi

echo "Final binary: ${full_bin}"
