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
  Runs the verified staged bootstrap pipeline using the active runtime binary.

FreeBSD / --target=freebsd-x86_64:
  Runs the FreeBSD seed bootstrap verifier using bin/freebsd/simple.

SimpleOS / --target=simpleos-x86_64:
  Runs the host-driven SimpleOS bootstrap target lane and stages guest artifacts
  for the underlying x86_64-simpleos lane.

Output: <output>/stage{1,2,3}/<arch>-<vendor>-<os>-<abi>/simple

Options:
  --backend=<name>   Backend for stage2/stage3/stage4 (default: llvm-lib)
  --output=<dir>     Output directory for bootstrap artifacts (default: build/bootstrap)
  --deploy           Copy the resulting/compiler artifact into bin/simple when supported
  --target=<triple>  Target platform (freebsd-x86_64 or simpleos-x86_64)
  --verbose          Accepted for compatibility
  --jobs=<n>         Accepted for compatibility
  --no-mcp           Skip MCP server builds (Stage 5)
  --keep-artifacts   Accepted for compatibility; artifacts are kept
  --no-verify        Accepted for compatibility; hash verification still runs
  --help             Show this help
EOF
}

backend="llvm-lib"
output_dir="build/bootstrap"
deploy=0
build_mcp=1
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
    --no-mcp)
      build_mcp=0
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

normalize_target() {
  case "${1-}" in
    simpleos-x86_64|x86_64-simpleos) echo "simpleos-x86_64" ;;
    *) echo "${1-}" ;;
  esac
}

target=$(normalize_target "${target}")

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

# SimpleOS target-lane dispatch (host-driven bootstrap to staged guest artifacts)
if [ "${target}" = "simpleos-x86_64" ]; then
  simpleos_args="--target=simpleos-x86_64 --build-dir=${output_dir}"
  if [ "${verbose}" -eq 1 ]; then
    simpleos_args="${simpleos_args} --verbose"
  fi
  if [ -n "${jobs}" ]; then
    simpleos_args="${simpleos_args} --jobs=${jobs}"
  fi
  if [ "${deploy}" -eq 1 ]; then
    simpleos_args="${simpleos_args} --package"
  fi
  echo "Bootstrap target lane: simpleos-x86_64"
  echo "  guest lane: x86_64-simpleos"
  exec "${repo_root}/bin/simple" run src/os/port/bootstrap_cross.spl -- ${simpleos_args}
fi

# Shared platform detection
. "${repo_root}/scripts/platform-detect.sh"
PLATFORM="${PLATFORM_TRIPLE}"
arch="${PLATFORM_ARCH}"
os="${PLATFORM_OS}"
echo "Platform: ${PLATFORM}"

log_dir="${output_dir}/logs/${PLATFORM}"
mkdir -p "${log_dir}"

run_logged() {
  label=$1
  shift
  log_file="${log_dir}/${label}.log"
  {
    echo "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] ${label}"
    echo "cwd: $(pwd)"
    echo "command: $*"
    echo ""
  } >"${log_file}"

  set +e
  "$@" >>"${log_file}" 2>&1
  status=$?
  set -e

  echo "  ${label} log: ${log_file}"
  if [ "${status}" -ne 0 ]; then
    echo "error: ${label} failed with exit ${status}" >&2
    if [ "${status}" -ge 128 ]; then
      signal=$((${status} - 128))
      echo "error: ${label} terminated by signal ${signal}" >&2
    fi
    echo "error: see log ${log_file}" >&2
    exit "${status}"
  fi
}

# ===========================================================================
# Bootstrap pipeline
# ===========================================================================

seed_bin="src/compiler_rust/target/bootstrap/simple"
native_all_lib="src/compiler_rust/target/bootstrap/libsimple_native_all.a"

# Detect stale seed OR stale runtime library: rebuild if any Rust source is
# newer than EITHER artifact.  The runtime library (libsimple_native_all.a) is
# linked into stage2/3/4 binaries and must include the latest stub filters,
# constructor stripping, and linker config.  Checking only the seed binary
# misses library staleness (hardlinks can mask mtime).
seed_stale=0
if [ -x "${seed_bin}" ]; then
  # Check against both seed binary AND runtime library
  check_against="${seed_bin}"
  if [ -f "${native_all_lib}" ]; then
    # Use whichever is OLDER as the reference — if either is stale, rebuild
    seed_mtime=$(stat -c '%Y' "${seed_bin}" 2>/dev/null || stat -f '%m' "${seed_bin}" 2>/dev/null || echo 0)
    lib_mtime=$(stat -c '%Y' "${native_all_lib}" 2>/dev/null || stat -f '%m' "${native_all_lib}" 2>/dev/null || echo 0)
    if [ "${lib_mtime}" -lt "${seed_mtime}" ] 2>/dev/null; then
      check_against="${native_all_lib}"
    fi
  fi
  stale_files=$(find src/compiler_rust -name '*.rs' -newer "${check_against}" -not -path '*/target/*' 2>/dev/null | head -1)
  if [ -n "${stale_files}" ]; then
    seed_stale=1
    echo "Seed/runtime stale (Rust sources changed since last build). Rebuilding..."
  fi
fi

# Detect LLVM 18 availability for llvm-lib backend
llvm_features=""
if [ "${backend}" = "llvm-lib" ] || [ "${backend}" = "llvm" ]; then
  llvm18_prefix="${LLVM_SYS_180_PREFIX:-/opt/homebrew/opt/llvm@18}"
  if [ -d "${llvm18_prefix}" ] && { [ -f "${llvm18_prefix}/lib/libLLVM.dylib" ] || [ -f "${llvm18_prefix}/lib/libLLVM-18.so" ]; }; then
    echo "LLVM 18 found: ${llvm18_prefix}"
    llvm_features="--features llvm"
    export LLVM_SYS_180_PREFIX="${llvm18_prefix}"
    # macOS needs LIBRARY_PATH for zstd and other Homebrew libs
    if [ "${host_os}" = "Darwin" ]; then
      export LIBRARY_PATH="${LIBRARY_PATH:+${LIBRARY_PATH}:}/opt/homebrew/lib"
      export SDKROOT="${SDKROOT:-$(xcrun --show-sdk-path 2>/dev/null || true)}"
    fi
  else
    echo "LLVM 18 not found (checked ${llvm18_prefix}); falling back to cranelift backend"
    backend="cranelift"
  fi
fi

if [ ! -x "${seed_bin}" ] || [ ! -f "${native_all_lib}" ] || [ "${seed_stale}" -eq 1 ]; then
  echo "Building Rust seed compiler + runtime library..."
  # Split into two cargo invocations to defeat feature unification:
  # `simple-native-all` enables `driver-hooks` on `simple-runtime`, which gates
  # out the `not(driver-hooks)` `#[no_mangle]` def of rt_cli_run_file. Building
  # both packages in a single `cargo build -p A -p B` call unifies features,
  # leaving the `simple-driver` bin with an undefined `rt_cli_run_file` symbol
  # (the C symbol is provided by `simple-native-all`, which the seed bin does
  # not link). Separate invocations keep simple-runtime's feature set per-bin.
  run_logged rust-seed-build cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver ${llvm_features}
  run_logged rust-native-all-build cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-native-all ${llvm_features}
fi

# Force manual bootstrap — ensures SIMPLE_RUNTIME_PATH is used for linking
# The full CLI `build bootstrap` command doesn't forward the runtime path
can_full_bootstrap=0

export SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap"
export SIMPLE_BOOTSTRAP=1
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
    "${seed_bin}" run src/app/cli/main.spl build bootstrap "--backend=${backend}" "--output=${output_dir}"
else
  # Bootstrap-only or missing — manual staged bootstrap via seed
  echo "  mode:     manual (seed → bootstrap_main → bootstrap_main)"
  if [ ! -x "${seed_bin}" ]; then
    echo "error: Rust seed required for manual bootstrap (${seed_bin})" >&2
    echo "Run: cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver" >&2
    exit 1
  fi

  # Stage 2: seed compiles bootstrap_main.spl
  # Always use cranelift for stage 2: the seed interpreter intercepts
  # --backend llvm-lib and dispatches to bootstrap_main.spl via the
  # interpreter, where rt_native_build is a stub that fails.  With
  # cranelift the seed uses its Rust handle_native_build directly.
  mkdir -p "${output_dir}/stage2/${PLATFORM}"
  echo "Stage 2: seed → bootstrap_main.spl"
  rm -rf .simple/native_cache/
  run_logged stage2-native-build env RUST_LOG="${RUST_LOG:-error}" "${seed_bin}" native-build \
    --backend cranelift \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
    --entry src/app/cli/bootstrap_main.spl \
    --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
    -o "${output_dir}/stage2/${PLATFORM}/simple"

  # Stage 3: stage2 recompiles bootstrap_main.spl (self-host verification)
  # Note: Stage3 is optional — the stage2 binary may lack features needed for
  # self-hosting (e.g., --entry-closure support in rt_native_build, or LLVM
  # symbol conflicts). When stage3 fails, we fall back to the seed for stage4.
  mkdir -p "${output_dir}/stage3/${PLATFORM}"
  echo "Stage 3: stage2 → bootstrap_main.spl (self-host)"
  rm -rf .simple/native_cache/

  stage3_ok=0
  set +e
  env RUST_LOG="${RUST_LOG:-error}" \
    LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
    "${output_dir}/stage2/${PLATFORM}/simple" native-build \
    --backend "${backend}" \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
    --entry src/app/cli/bootstrap_main.spl \
    --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
    -o "${output_dir}/stage3/${PLATFORM}/simple" \
    >"${log_dir}/stage3-native-build.log" 2>&1
  stage3_status=$?
  set -e

  echo "  stage3-native-build log: ${log_dir}/stage3-native-build.log"
  if [ "${stage3_status}" -eq 0 ] && [ -x "${output_dir}/stage3/${PLATFORM}/simple" ]; then
    stage3_ok=1
    echo "  Stage 3 succeeded"
  else
    echo "  warning: stage3 self-host failed (exit ${stage3_status}); using seed for stage 4"
  fi
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

if [ ! -x "${stage2}" ]; then
  echo "error: stage2 binary was not produced" >&2
  exit 1
fi

# Decide which compiler to use for stage 4
stage4_is_seed=0
if [ "${stage3_ok:-0}" -eq 1 ] && [ -x "${stage3}" ]; then
  hash2=$(sha256sum "${stage2}" | awk '{print $1}')
  hash3=$(sha256sum "${stage3}" | awk '{print $1}')
  echo "stage2 sha256: ${hash2}"
  echo "stage3 sha256: ${hash3}"
  if [ "${hash2}" != "${hash3}" ]; then
    echo "warning: stage2 and stage3 hashes differ (expected when runtime is embedded)"
    echo "  Using stage2 (with runtime) for stage 4"
    stage_for_build="${stage2}"
  else
    echo "Bootstrap verification passed."
    stage_for_build="${stage3}"
  fi
else
  echo "Stage 3 unavailable — using seed for stage 4"
  stage_for_build="${seed_bin}"
  stage4_is_seed=1
fi

# When stage 4 uses the Rust seed, --backend llvm-lib triggers the
# interpreter dispatch path (native_build_should_use_simple returns true),
# where rt_native_build is a stub that fails.  Use cranelift for the seed.
# Compiled binaries (stage2/stage3) call rt_native_build from libsimple_native_all.a
# and handle all backends correctly.
if [ "${stage4_is_seed}" -eq 1 ]; then
  stage4_backend="cranelift"
else
  stage4_backend="${backend}"
fi

# ===========================================================================
# Stage 4: Compile full CLI (main.spl) with verified bootstrap compiler
# ===========================================================================

echo "Stage 4: compiling full CLI (main.spl) with bootstrap compiler..."
full_dir="${output_dir}/full/${PLATFORM}"
mkdir -p "${full_dir}"
rm -rf .simple/native_cache/
run_logged stage4-native-build env RUST_LOG="${RUST_LOG:-error}" \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  "${stage_for_build}" native-build \
  --backend "${stage4_backend}" \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure \
  --entry src/app/cli/main.spl \
  --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
  -o "${full_dir}/simple"

full_bin="${full_dir}/simple"
if [ ! -x "${full_bin}" ]; then
  echo "error: failed to compile full CLI binary from main.spl" >&2
  exit 1
fi

echo "Full CLI binary: ${full_bin}"

# ===========================================================================
# Stage 5: Compile MCP servers (optional, skip with --no-mcp)
# ===========================================================================

mcp_build_ok=1
if [ "${build_mcp}" -eq 1 ]; then
  echo "Stage 5: compiling MCP servers..."

  # Build each MCP server with non-blocking failure.
  # Note: run commands directly (not via run_logged) because run_logged
  # calls exit on failure, and MCP build failure must be non-blocking.
  mcp_stage=0
  for mcp_entry in "simple_mcp_server:src/app/mcp/main.spl" \
                    "simple_lsp_mcp_server:src/app/simple_lsp_mcp/main.spl"; do
    mcp_stage=$((mcp_stage + 1))
    mcp_name="${mcp_entry%%:*}"
    mcp_spl="${mcp_entry#*:}"
    mcp_log="stage5${mcp_stage}-mcp-native-build"

    echo "  Stage 5${mcp_stage}: ${mcp_name}"
    rm -rf .simple/native_cache/
    set +e
    env RUST_LOG="${RUST_LOG:-error}" \
      LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
      "${stage_for_build}" native-build \
      --backend "${stage4_backend}" \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure \
      --entry "${mcp_spl}" \
      --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
      -o "${full_dir}/${mcp_name}" \
      >"${log_dir}/${mcp_log}.log" 2>&1
    mcp_status=$?
    set -e
    echo "  ${mcp_log} log: ${log_dir}/${mcp_log}.log"
    if [ "${mcp_status}" -ne 0 ]; then
      mcp_build_ok=0
      echo "  WARNING: ${mcp_name} build failed (exit ${mcp_status})"
    elif [ ! -s "${full_dir}/${mcp_name}" ]; then
      mcp_build_ok=0
      echo "  WARNING: ${mcp_name} produced a zero-byte file"
    else
      echo "  ${mcp_name}: ${full_dir}/${mcp_name}"
    fi
  done
else
  echo "Skipping MCP server builds (--no-mcp)"
fi

# ===========================================================================
# Deploy
# ===========================================================================

if [ "${deploy}" -eq 1 ]; then
  deploy_dir="bin/release/${PLATFORM}"
  mkdir -p "${deploy_dir}"
  install -m755 "${full_bin}" "${deploy_dir}/simple"
  echo "Deployed full CLI binary to ${deploy_dir}/simple"

  # Deploy MCP servers if they were built successfully
  if [ "${build_mcp}" -eq 1 ] && [ "${mcp_build_ok}" -eq 1 ]; then
    for mcp_bin_name in simple_mcp_server simple_lsp_mcp_server; do
      if [ -x "${full_dir}/${mcp_bin_name}" ] && [ -s "${full_dir}/${mcp_bin_name}" ]; then
        install -m755 "${full_dir}/${mcp_bin_name}" "${deploy_dir}/${mcp_bin_name}"
        echo "Deployed ${mcp_bin_name} to ${deploy_dir}/${mcp_bin_name}"
      fi
    done
  fi

  # Recreate wrapper/launcher entrypoints (bin/simple plus release links)
  "${repo_root}/scripts/setup.sh"
fi

echo "Final binary: ${full_bin}"

# ===========================================================================
# Exit status — reflect self-host verification result
# ===========================================================================

if [ "${stage3_ok:-0}" -eq 0 ]; then
  echo ""
  echo "WARNING: Bootstrap produced a binary but self-host verification (stage 3) failed."
  echo "  The stage2 binary cannot yet recompile itself (LIM-010: LLVM symbol conflicts)."
  echo "  Stage 4 used the Rust seed instead of the self-hosted compiler."
  echo "  This is a known limitation — see doc/09_report/bootstrap_crash_report_2026_04_01.md"
  exit 2
fi
