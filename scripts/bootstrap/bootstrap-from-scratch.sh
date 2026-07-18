#!/bin/sh
set -eu

# Bootstrap wrapper for Linux, macOS, Windows/MSYS2, and FreeBSD.
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

Linux / macOS / Windows (Git Bash or MSYS2) / FreeBSD:
  Runs the verified staged bootstrap pipeline using the active runtime binary.

SimpleOS / --target=simpleos-x86_64:
  Runs the host-driven SimpleOS bootstrap target lane and stages guest artifacts
  for the underlying x86_64-simpleos lane.

Output: <output>/stage{1,2,3}/<arch>-<vendor>-<os>-<abi>/simple

Options:
  --backend=<name>   Backend for stage2/stage3/stage4 (default: llvm; cranelift also supported)
  --output=<dir>     Output directory for bootstrap artifacts (default: build/bootstrap)
  --full-bootstrap   Rebuild the Rust seed/runtime when missing or stale, then
                     rebuild the pure-Simple stages. Without this flag bootstrap
                     never runs cargo and reuses the existing Rust seed.
  --pure-simple      Compatibility alias for the default no-Rust rebuild mode.
  --mode=<name>      Pure-Simple build mode: dynload or one-binary
                     (default: dynload; env: SIMPLE_BOOTSTRAP_MODE)
                     SIMPLE_NO_STUB_FALLBACK=1 also makes staged failures fatal
  --full-cli         Relink the full CLI after the staged pure-Simple build
                     (supported on native Linux and macOS hosts).
                     Implied by --deploy and one-binary mode.
  --fresh-cache      Clear the dynload native cache once before rebuilding
  --deploy           Copy the resulting/compiler artifact into bin/simple when supported
  --release          Deploy, then run the release-blocking whole test suite
  --target=<triple>  Target platform (freebsd-x86_64 or simpleos-x86_64)
  --verbose          Accepted for compatibility
  --jobs=<n|full|half|min|auto>
                     Native build workers (default: half CPUs locally, 2 on GitHub Actions)
  --no-mcp           Skip MCP server builds (Stage 5)
  --keep-artifacts   Accepted for compatibility; artifacts are kept
  --no-verify        Accepted for compatibility; hash verification still runs
  --help             Show this help
EOF
}

backend="llvm"
output_dir="build/bootstrap"
deploy=0
build_mcp=1
target=""
verbose=0
jobs=""
pure_simple=0
full_bootstrap=0
full_cli=0
fresh_cache=0
release_tests=0
bootstrap_mode="${SIMPLE_BOOTSTRAP_MODE:-dynload}"
case "${SIMPLE_NO_STUB_FALLBACK:-0}" in
  1|true|yes|on) strict_bootstrap=1 ;;
  *) strict_bootstrap=0 ;;
esac

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
    --release)
      release_tests=1
      deploy=1
      ;;
    --full-bootstrap)
      full_bootstrap=1
      ;;
    --pure-simple)
      pure_simple=1
      ;;
    --full-cli)
      full_cli=1
      ;;
    --fresh-cache|--no-cache)
      fresh_cache=1
      ;;
    --mode=*)
      bootstrap_mode=${1#*=}
      if [ -z "${bootstrap_mode}" ]; then
        bootstrap_mode=dynload
      fi
      ;;
    --mode)
      shift
      if [ "$#" -eq 0 ]; then
        echo "error: --mode requires dynload or one-binary" >&2
        usage >&2
        exit 1
      fi
      bootstrap_mode=$1
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

case "${backend}" in
  llvm|llvm-lib|cranelift) ;;
  *)
    echo "error: unsupported bootstrap backend '${backend}' (expected llvm, llvm-lib, or cranelift)" >&2
    exit 1
    ;;
esac

case "${bootstrap_mode}" in
  dynload|one-binary) ;;
  *)
    echo "error: unknown --mode '${bootstrap_mode}' (expected dynload or one-binary)" >&2
    exit 1
    ;;
esac

if [ "${pure_simple}" -eq 1 ] && [ "${full_bootstrap}" -eq 1 ]; then
  echo "error: --pure-simple and --full-bootstrap conflict" >&2
  exit 1
fi

if [ "${deploy}" -eq 1 ] || [ "${bootstrap_mode}" = "one-binary" ]; then
  full_cli=1
fi

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

if [ "${full_cli}" -eq 1 ]; then
  case "${host_os}" in
    Linux|Darwin) ;;
    *)
      echo "error: Stage 4 full-CLI capsule preparation requires native Linux or macOS" >&2
      exit 1
      ;;
  esac
fi

# FreeBSD must build inside FreeBSD. Linux hosts use the QEMU verifier, which
# syncs the repository and invokes this same wrapper in the guest.
if [ "${target}" = "freebsd-x86_64" ] && [ "${host_os}" != "FreeBSD" ]; then
  echo "error: FreeBSD bootstrap must run inside FreeBSD." >&2
  echo "  Linux host: sh scripts/check/check-freebsd-bootstrap-qemu.shs --full" >&2
  exit 1
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
. "${repo_root}/scripts/setup/platform-detect.shs"
PLATFORM="${PLATFORM_TRIPLE}"
arch="${PLATFORM_ARCH}"
os="${PLATFORM_OS}"
echo "Platform: ${PLATFORM}"

exe_suffix=""
archive_prefix="lib"
archive_suffix=".a"
if [ "${os}" = "windows" ]; then
  exe_suffix=".exe"
  if [ "${SIMPLE_LINKER_FLAVOR:-}" = "msvc" ]; then
    archive_prefix=""
    archive_suffix=".lib"
  elif [ "${SIMPLE_LINKER_FLAVOR:-}" = "gnu" ]; then
    archive_prefix="lib"
    archive_suffix=".a"
  elif [ "${PLATFORM_ABI}" = "gnu" ]; then
    archive_prefix="lib"
    archive_suffix=".a"
  else
    archive_prefix=""
    archive_suffix=".lib"
  fi
fi

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  elif command -v sha256 >/dev/null 2>&1; then
    sha256 -q "$1"
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | awk '{print $NF}'
  else
    echo "error: no SHA-256 tool found (sha256sum, shasum, sha256, or openssl)" >&2
    return 1
  fi
}

hash_stream() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 | awk '{print $1}'
  elif command -v sha256 >/dev/null 2>&1; then
    sha256 | awk '{print $NF}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 | awk '{print $NF}'
  else
    echo "error: no SHA-256 tool found (sha256sum, shasum, sha256, or openssl)" >&2
    return 1
  fi
}

hash_path_list() {
  while IFS= read -r file; do
    printf '%s  %s\n' "$(hash_file "${file}")" "${file}"
  done
}

run_timeout() {
  timeout_seconds=$1
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout "${timeout_seconds}" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout "${timeout_seconds}" "$@"
  else
    "$@"
  fi
}

run_timeout_kill() {
  timeout_seconds=$1
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout -k 1s "${timeout_seconds}s" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout -k 1s "${timeout_seconds}s" "$@"
  else
    "$@"
  fi
}

absolute_path() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *) printf '%s/%s\n' "${repo_root}" "$1" ;;
  esac
}

if [ -n "${LLVM_PREFIX:-}" ] && [ -d "${LLVM_PREFIX}/bin" ]; then
  case ":${PATH}:" in
    *":${LLVM_PREFIX}/bin:"*) ;;
    *) export PATH="${LLVM_PREFIX}/bin:${PATH}" ;;
  esac
fi

log_dir="${output_dir}/logs/${PLATFORM}"
mkdir -p "${log_dir}"

host_cpus=$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || echo 2)
case "${host_cpus}" in
  ''|*[!0-9]*) host_cpus=2 ;;
esac
case "${jobs}" in
  ""|auto)
    jobs=""
    ;;
  full)
    jobs="${host_cpus}"
    ;;
  half)
    jobs=$((host_cpus / 2))
    if [ "${jobs}" -lt 1 ]; then
      jobs=1
    fi
    ;;
  min|minimal|minimum)
    jobs=1
    ;;
esac
if [ -z "${jobs}" ]; then
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    jobs=2
  else
    jobs=$((host_cpus / 2))
    if [ "${jobs}" -lt 1 ]; then
      jobs=1
    fi
  fi
fi
case "${jobs}" in
  ''|*[!0-9]*|0)
    echo "error: --jobs must be a positive integer" >&2
    exit 1
    ;;
esac
echo "Native build jobs: ${jobs} (host CPUs: ${host_cpus})"
selfhost_jobs="${jobs}"
if [ "${selfhost_jobs}" -gt 2 ]; then
  selfhost_jobs=2
fi

native_cache_dir="${output_dir}/native_cache"
native_cache_stamp="${native_cache_dir}/bootstrap-wide-inputs.sha256"
native_cache_freshened=0

bootstrap_wide_inputs_hash() {
  {
    # Module fingerprints cover source edits, but unchanged modules must also
    # be rebuilt when the compiler/runtime that emits their objects changes.
    printf 'platform=%s backend=%s mode=%s stub_fallback=forbidden\n' "${PLATFORM}" "${backend}" "${bootstrap_mode}"
    printf 'seed-inputs=%s\n' "${seed_inputs_fingerprint:-missing}"
    find src/compiler -name '*.spl' -type f -print 2>/dev/null \
      | LC_ALL=C sort | hash_path_list
    env | LC_ALL=C sort | awk '/^SIMPLE_.*(AOP|MDSOC|WEAV|LOAD|INTERPRET|EXECUTION|LIB|NATIVE_BUILD)/ { print }'
  } | hash_stream
}

prepare_native_cache() {
  label=$1
  if [ "${bootstrap_mode}" = "one-binary" ]; then
    echo "  ${label}: clearing native cache (one-binary mode)"
    rm -rf "${native_cache_dir}/"
    return
  fi

  mkdir -p "${native_cache_dir}"
  current_hash=$(bootstrap_wide_inputs_hash)
  if [ "${fresh_cache}" -eq 1 ] && [ "${native_cache_freshened}" -eq 0 ]; then
    echo "  ${label}: clearing native cache (--fresh-cache)"
    rm -rf "${native_cache_dir}/"
    mkdir -p "${native_cache_dir}"
    printf '%s\n' "${current_hash}" > "${native_cache_stamp}"
    native_cache_freshened=1
    return
  fi
  if [ ! -f "${native_cache_stamp}" ] || [ "$(cat "${native_cache_stamp}" 2>/dev/null)" != "${current_hash}" ]; then
    echo "  ${label}: clearing native cache (platform/backend/AOP build context changed)"
    rm -rf "${native_cache_dir}/"
    mkdir -p "${native_cache_dir}"
    printf '%s\n' "${current_hash}" > "${native_cache_stamp}"
  else
    echo "  ${label}: reusing native cache (dynload mode)"
  fi
}

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

CANDIDATE_FRONTEND_ROOT=${repo_root}
COMPILER_PROBE_TIMEOUT_SECONDS=5
COMPILER_BUILD_TIMEOUT_SECONDS=60
COMPILER_EXEC_TIMEOUT_SECONDS=5
COMPILER_CHECK_KILL_GRACE_SECONDS=1
. "${repo_root}/scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs"

bootstrap_stage_sanity() (
  candidate=$1
  version=$(run_timeout 10 "${candidate}" --version 2>&1) || return 1
  [ "${version}" = "simple-bootstrap 1.0.0-beta" ] || return 1
  if unsupported=$(run_timeout 10 "${candidate}" run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl 2>&1); then
    return 1
  else
    unsupported_status=$?
  fi
  [ "${unsupported_status}" -eq 1 ] || return 1
  case "${unsupported}" in
    *"unknown command 'run'"*) ;;
    *) return 1 ;;
  esac
  CANDIDATE_FRONTEND_BACKEND="${backend}" candidate_frontend_smoke "${candidate}"
)

bootstrap_native_build_main() {
  compiler=$1
  output=$2
  env RUST_LOG="${RUST_LOG:-error}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_BOOTSTRAP_STAGE4=1 \
    SIMPLE_NATIVE_BUILD_TARGET="${PLATFORM}" \
    SIMPLE_NATIVE_BUILD_THREADS="${selfhost_jobs}" \
    SIMPLE_NATIVE_BUILD_CACHE_DIR="${native_cache_dir}" \
    SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap" \
    LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BINARY="$(absolute_path "${compiler}")" \
    "${compiler}" native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle core-c-bootstrap \
    --source src/compiler --source src/app --source src/lib --source examples/10_tooling \
    --entry-closure \
    --low-memory \
    --threads "${selfhost_jobs}" \
    --cache-dir "${native_cache_dir}" \
    --mode one-binary \
    --entry src/app/cli/main.spl \
    --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
    -o "${output}"
}

# ===========================================================================
# Bootstrap pipeline
# ===========================================================================

seed_bin="src/compiler_rust/target/bootstrap/simple${exe_suffix}"
native_all_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_native_all${archive_suffix}"
compiler_backfill_lib="src/compiler_rust/target/bootstrap/${archive_prefix}simple_compiler_backfill${archive_suffix}"

# Detect stale seed OR stale runtime library by CONTENT, not mtime.
#
# The previous check used `find -newer` (mtime). jj/git operations (reconcile,
# checkout, working-copy snapshots) routinely bump .rs mtimes WITHOUT changing
# content, which made every bootstrap spuriously recompile ~11 Rust crates
# (~5 min of pure waste; measured 2026-06-14: 286s, 0 content changes).
#
# seed_inputs_hash fingerprints everything that determines the seed binary +
# runtime library: all Rust sources, every Cargo.toml, Cargo.lock, the build
# profile/backend/features, and the rustc version. A stamp file beside the seed
# records the fingerprint of the inputs the current seed was built from; we
# rebuild only when the fingerprint differs (or is missing) — never on mtime
# churn. Any doubt (missing stamp, hash failure → empty mismatch) rebuilds: a
# stale seed would silently miscompile, which is worse than a slow build.
seed_stamp="${seed_bin}.inputs.sha256"
seed_inputs_hash() {
  {
    find src/compiler_rust \( -type d -name 'target*' -o -path src/compiler_rust/vendor \) -prune -o \
      \( -name '*.rs' -o -name 'Cargo.toml' \) -type f -print 2>/dev/null \
      | LC_ALL=C sort | hash_path_list
    find src/runtime \( -name '*.c' -o -name '*.h' \) -type f -print 2>/dev/null \
      | LC_ALL=C sort | hash_path_list
    printf '%s  %s\n' "$(hash_file src/compiler_rust/Cargo.lock)" src/compiler_rust/Cargo.lock
    printf 'profile=bootstrap backend=%s features=%s\n' "${backend}" "${llvm_features}"
    rustc -V 2>/dev/null
  } | hash_stream
}
seed_stale=0
rust_rebuilt=0
# (content-hash staleness gate runs below, after backend/llvm_features settle)

# Detect LLVM 18 availability for LLVM backends.
llvm_features=""
if [ "${backend}" = "llvm-lib" ] || [ "${backend}" = "llvm" ]; then
  # LLVM is resolved once by the shared platform interface
  # (scripts/setup/platform-detect.shs, sourced above), which also exports
  # LLVM_SYS_<major>0_PREFIX and SIMPLE_LLVM_PATH for the Rust build and Simple runtime.
  if [ "${LLVM_FOUND:-0}" = "1" ]; then
    echo "LLVM ${LLVM_VERSION} found: ${LLVM_PREFIX} (lib: ${LLVM_LIB})"
    llvm_features="--features llvm"
    # macOS needs LIBRARY_PATH for zstd and other Homebrew libs
    if [ "${host_os}" = "Darwin" ]; then
      brew_prefix="$(brew --prefix 2>/dev/null || true)"
      if [ -n "${brew_prefix}" ]; then
        export HOMEBREW_PREFIX="${brew_prefix}"
        export LIBRARY_PATH="${LIBRARY_PATH:+${LIBRARY_PATH}:}${brew_prefix}/lib"
      fi
      export SDKROOT="${SDKROOT:-$(xcrun --show-sdk-path 2>/dev/null || true)}"
    fi
  else
    echo "error: LLVM not found (shared platform detection: scripts/setup/platform-detect.shs, versions: ${LLVM_VERSIONS:-18})" >&2
    echo "error: install LLVM or select --backend=cranelift explicitly" >&2
    exit 1
  fi
fi

# Content-hash staleness gate (see seed_inputs_hash above). Runs here so the
# backend/features are final before they enter the fingerprint. If the seed or
# runtime library is missing, the cargo branch below rebuilds regardless.
seed_inputs_fingerprint=$(seed_inputs_hash)
if [ -x "${seed_bin}" ] && [ -f "${native_all_lib}" ]; then
  if [ ! -f "${seed_stamp}" ] || [ "$(cat "${seed_stamp}" 2>/dev/null)" != "${seed_inputs_fingerprint}" ]; then
    seed_stale=1
    if [ "${full_bootstrap}" -eq 1 ]; then
      echo "Seed/runtime stale (Rust source content changed since last build). Full bootstrap will rebuild Rust."
    else
      echo "WARNING: Seed/runtime stale, but this is not --full-bootstrap; reusing the existing Rust seed."
    fi
  else
    echo "Seed/runtime current (input content hash matches); skipping Rust rebuild."
  fi
fi

if [ "${full_bootstrap}" -eq 0 ]; then
  # Default/pure-Simple rebuild: reuse the existing Rust seed and runtime
  # library, never invoke cargo. Whether the existing seed CAN build the changed
  # pure-Simple is proven by Stage 2 below: if the new .spl needs a Rust feature
  # the seed lacks, Stage 2 fails — rerun with --full-bootstrap.
  if [ ! -x "${seed_bin}" ] || [ ! -f "${native_all_lib}" ]; then
    echo "error: bootstrap needs an existing Rust seed and runtime library:" >&2
    echo "  seed:    ${seed_bin}" >&2
    echo "  runtime: ${native_all_lib}" >&2
    echo "Normal bootstrap does not rebuild Rust. Re-run with --full-bootstrap to build them." >&2
    exit 1
  fi
  if [ "${full_cli}" -eq 1 ] && [ ! -f "${compiler_backfill_lib}" ]; then
    echo "error: full CLI bootstrap needs the compiler backfill archive: ${compiler_backfill_lib}" >&2
    echo "Re-run with --full-bootstrap to build it." >&2
    exit 1
  fi
  if [ "${full_cli}" -eq 1 ] && [ "${seed_stale}" -eq 1 ]; then
    echo "error: full CLI bootstrap refuses a stale compiler backfill; re-run with --full-bootstrap" >&2
    exit 1
  fi
  if [ "${seed_stale}" -eq 1 ]; then
    echo "WARNING: Rust sources changed; reusing the existing seed because --full-bootstrap was not given."
  fi
  echo "Pure-Simple mode: ${bootstrap_mode}; reusing Rust seed, rebuilding only pure-Simple stages."
elif [ ! -x "${seed_bin}" ] || [ ! -f "${native_all_lib}" ] || [ "${seed_stale}" -eq 1 ]; then
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
  rust_rebuilt=1
  # Record the fingerprint of the inputs we just built from, so the next run
  # can skip cargo when nothing actually changed (only written after a real
  # rebuild — never in pure-Simple or hash-match-skip paths).
  seed_inputs_hash > "${seed_stamp}"
fi

if [ "${full_bootstrap}" -eq 1 ] \
   && { [ ! -f "${compiler_backfill_lib}" ] || [ "${seed_stale}" -eq 1 ] || [ "${rust_rebuilt}" -eq 1 ]; }; then
  run_logged rust-compiler-backfill-build cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-compiler-backfill
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
echo "  ps-mode:  ${bootstrap_mode}"
echo "  output:   ${output_dir}"
if [ "${full_bootstrap}" -eq 1 ]; then
  echo "  rust:     full-bootstrap enabled; seed/runtime may be rebuilt"
else
  echo "  rust:     seed/runtime reuse only; cargo disabled"
fi

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
    echo "Run: scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap" >&2
    exit 1
  fi

  # Stage 2: seed compiles bootstrap_main.spl
  # Stage 2 uses the configured backend; LLVM is the default and Cranelift is
  # an explicit supported alternative.
  mkdir -p "${output_dir}/stage2/${PLATFORM}"
  echo "Stage 2: seed → bootstrap_main.spl"
  prepare_native_cache stage2
  # Stage 2 failure is reported before Stage 3; no later stage may claim it.
  # the self-hosting frontend now fails closed instead of linking a ret-0 stub
  # (doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md), so a
  # stage-2 build error must not abort the whole pipeline.
  stage2_bin="${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}"
  stage3_bin="${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}"
  rm -f "${stage2_bin}" "${stage3_bin}"
  set +e
  env RUST_LOG="${RUST_LOG:-error}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_NATIVE_BUILD_RUST=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    SIMPLE_BINARY="$(absolute_path "${seed_bin}")" \
    "${seed_bin}" native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle rust-hosted \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
    --threads "${jobs}" \
    --cache-dir "${native_cache_dir}" \
    --mode "${bootstrap_mode}" \
    --entry src/app/cli/bootstrap_main.spl \
    --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
    -o "${stage2_bin}" \
    >"${log_dir}/stage2-native-build.log" 2>&1
  stage2_status=$?
  set -e
  echo "  stage2-native-build log: ${log_dir}/stage2-native-build.log"
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    echo "  Stage 2: running bootstrap compiler sanity"
    if ! bootstrap_stage_sanity "${stage2_bin}"; then
      echo "error: Stage 2 bootstrap compiler sanity failed" >&2
      stage2_status=2
      rm -f "${stage2_bin}"
    fi
  fi
  if [ "${stage2_status}" -ne 0 ]; then
    if [ "${strict_bootstrap}" -eq 1 ]; then
      echo "error: strict bootstrap stage2 failed (exit ${stage2_status}); refusing seed fallback" >&2
      exit "${stage2_status}"
    fi
    echo "  warning: stage2 native-build failed (exit ${stage2_status}); Stage 3/full CLI unavailable" >&2
    echo "  warning: see doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md" >&2
  fi

  # Stage 3: stage2 recompiles bootstrap_main.spl (self-host verification)
  # Note: Stage3 is optional — the stage2 binary may lack features needed for
  # self-hosting (e.g., --entry-closure support in rt_native_build, or LLVM
  # symbol conflicts). When Stage 3 fails, the wrapper stops before Stage 4.
  mkdir -p "${output_dir}/stage3/${PLATFORM}"
  echo "Stage 3: stage2 → bootstrap_main.spl (self-host)"
  prepare_native_cache stage3

  stage3_ok=0
  rm -f "${stage3_bin}"
  set +e
  [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ] && \
  env RUST_LOG="${RUST_LOG:-error}" \
    SIMPLE_BOOTSTRAP=1 \
    SIMPLE_NO_DEPRECATED_WARNINGS=1 \
    SIMPLE_NATIVE_BUILD_RUST=1 \
    SIMPLE_NO_STUB_FALLBACK=1 \
    LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
    SIMPLE_BINARY="$(absolute_path "${stage2_bin}")" \
    "${stage2_bin}" native-build \
    --target "${PLATFORM}" \
    --backend "${backend}" \
    --runtime-bundle rust-hosted \
    --source src/compiler --source src/app --source src/lib \
    --entry-closure \
    --threads "${selfhost_jobs}" \
    --cache-dir "${native_cache_dir}" \
    --mode "${bootstrap_mode}" \
    --entry src/app/cli/bootstrap_main.spl \
    --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
    -o "${stage3_bin}" \
    >"${log_dir}/stage3-native-build.log" 2>&1
  stage3_status=$?
  set -e

  echo "  stage3-native-build log: ${log_dir}/stage3-native-build.log"
  if [ "${stage3_status}" -eq 0 ] && [ -x "${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}" ]; then
    if bootstrap_stage_sanity "${stage3_bin}"; then
      stage3_ok=1
      echo "  Stage 3 succeeded and passed bootstrap compiler sanity"
    else
      stage3_status=2
      rm -f "${stage3_bin}"
      echo "error: Stage 3 bootstrap compiler sanity failed" >&2
    fi
  fi
  if [ "${stage3_ok}" -ne 1 ]; then
    if [ "${strict_bootstrap}" -eq 1 ]; then
      echo "error: strict bootstrap stage3 failed; refusing seed fallback" >&2
      if [ "${stage3_status}" -ne 0 ]; then
        exit "${stage3_status}"
      fi
      exit 2
    fi
    if [ "${stage3_status}" -eq 0 ]; then
      echo "  warning: stage3 self-host produced no executable; Stage 4 unavailable"
    else
      echo "  warning: stage3 self-host failed (exit ${stage3_status}); Stage 4 unavailable"
    fi
  fi

  stage2_capability_ok=0
  stage2_capability_bin="${output_dir}/stage2-capability-${PLATFORM}${exe_suffix}"
  stage2_capability_cache="${output_dir}/stage2-capability-cache"
  rm -f "${stage2_capability_bin}"
  if [ "${stage2_status}" -eq 0 ] && [ -x "${stage2_bin}" ]; then
    set +e
    env SIMPLE_BOOTSTRAP=1 \
      SIMPLE_NO_DEPRECATED_WARNINGS=1 \
      "${stage2_bin}" native-build \
      --target "${PLATFORM}" \
      --backend "${backend}" \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure \
      --threads 1 \
      --cache-dir "${stage2_capability_cache}" \
      --mode "${bootstrap_mode}" \
      --entry test/04_smoke/windows_native_hello.spl \
      --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
      -o "${stage2_capability_bin}" \
      >"${log_dir}/stage2-capability.log" 2>&1
    stage2_capability_status=$?
    set -e
    if [ "${stage2_capability_status}" -eq 0 ] && [ -x "${stage2_capability_bin}" ]; then
      if stage2_capability_output="$(run_timeout 30 "${stage2_capability_bin}" 2>/dev/null)"; then
        if [ "${stage2_capability_output}" = "windows native hello" ]; then
          stage2_capability_ok=1
          echo "  Stage 2 native-build capability passed"
        fi
      fi
    fi
  fi
  if [ "${stage2_capability_ok}" -ne 1 ]; then
    echo "  warning: Stage 2 native-build capability failed; using seed for stage 4" >&2
    echo "  warning: see ${log_dir}/stage2-capability.log" >&2
  fi
fi

# Locate stage outputs — check new layout first, fall back to flat
if [ -x "${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}" ]; then
  stage2="${output_dir}/stage2/${PLATFORM}/simple${exe_suffix}"
  stage3="${output_dir}/stage3/${PLATFORM}/simple${exe_suffix}"
elif [ -x "${output_dir}/simple_stage2" ]; then
  stage2="${output_dir}/simple_stage2"
  stage3="${output_dir}/simple_stage3"
else
  stage2=""
  stage3=""
fi

if [ ! -x "${stage2}" ]; then
  echo "warning: stage2 binary was not produced; Stage 3/full CLI unavailable" >&2
  stage3_ok=0
fi

# Decide which compiler to use for stage 4
stage4_is_seed=0
if [ "${stage3_ok:-0}" -eq 1 ] && [ -x "${stage3}" ]; then
  hash2=$(hash_file "${stage2}")
  hash3=$(hash_file "${stage3}")
  echo "stage2 sha256: ${hash2}"
  echo "stage3 sha256: ${hash3}"
  if [ "${hash2}" != "${hash3}" ]; then
    echo "warning: stage2 and stage3 hashes differ (expected when runtime is embedded)"
    if [ "${stage2_capability_ok:-0}" -eq 1 ]; then
      echo "  Using capability-verified Stage 2 with embedded runtime for stage 4"
      stage_for_build="${stage2}"
    else
      echo "  No capability-verified compiler is available for stage 4"
      stage_for_build=""
      stage4_is_seed=1
    fi
  else
    echo "Bootstrap verification passed."
    stage_for_build="${stage3}"
  fi
else
  if [ "${stage2_capability_ok:-0}" -eq 1 ] && [ -x "${stage2}" ]; then
    echo "Stage 3 unavailable — using capability-verified Stage 2 for stage 4"
    stage_for_build="${stage2}"
  else
    echo "Stage 3 unavailable — no verified compiler for Stage 4"
    stage_for_build=""
    stage4_is_seed=1
  fi
fi

# Fast iteration stops after the pure-Simple dynload stages. Relinking the
# complete CLI is explicit because it is the dominant cost and is unnecessary
# for ordinary compiler/app/lib edits that are consumed through dynload caches.
if [ "${full_cli}" -eq 0 ]; then
  echo "Pure-Simple dynload build complete; full CLI relink skipped."
  echo "  cache: ${native_cache_dir}"
  echo "  use --full-cli, --deploy, or --mode=one-binary to relink"
  if [ "${stage3_ok:-0}" -eq 0 ]; then
    exit 2
  fi
  exit 0
fi

if [ "${stage4_is_seed}" -eq 1 ]; then
  echo "error: full CLI build requires a verified pure-Simple stage2/stage3 compiler; refusing seed fallback" >&2
  exit 2
fi
# ===========================================================================
# Stage 4: Compile full CLI (main.spl) with verified bootstrap compiler
# ===========================================================================

echo "Stage 4: compiling full CLI (main.spl) with bootstrap compiler..."
full_dir="${output_dir}/full/${PLATFORM}"
mkdir -p "${full_dir}"
prepare_native_cache stage4
rm -f "${full_dir}/simple${exe_suffix}"
run_logged stage4-native-build bootstrap_native_build_main \
  "${stage_for_build}" "${full_dir}/simple${exe_suffix}"

full_bin="${full_dir}/simple${exe_suffix}"
if [ ! -x "${full_bin}" ]; then
  echo "error: failed to compile full CLI binary from main.spl" >&2
  exit 1
fi

install -m755 "${seed_bin}" "${full_dir}/simple_seed${exe_suffix}"

stage4_smoke="$(run_timeout 30 "${full_bin}" -c 'print(1+1)' 2>/dev/null)"
if [ "${stage4_smoke}" != "2" ]; then
  echo "error: stage4 binary failed smoke test (-c 'print(1+1)' -> '${stage4_smoke}')" >&2
  exit 1
fi

# `-c` can succeed by delegating to the sibling Rust seed even when the newly
# linked full CLI cannot read or compile source files itself. MCP/LSP startup
# needs the latter, so reject such candidates before deployment.
if ! run_timeout 60 env SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
    "${full_bin}" check src/app/cli/bootstrap_main.spl >/dev/null 2>&1; then
  echo "error: stage4 binary failed source-check smoke (MCP/LSP would not start)" >&2
  exit 1
fi

if ! simple_binary_is_valid "${full_bin}"; then
  echo "error: stage4 binary failed the current frontend candidate gate" >&2
  exit 1
fi

run_logged stage4-redeploy-gate run_timeout_kill 180 sh \
  scripts/check/cert/redeploy_gate/redeploy_gate.shs "${full_bin}"

run_logged stage4-essential-tools-smoke run_timeout_kill 180 env \
  SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
  sh scripts/check/check-bootstrap-essential-tools-smoke.shs

echo "Stage 4b: compiling cached UI backend..."
ui_backend_bin="${full_dir}/simple_ui_backend${exe_suffix}"
prepare_native_cache stage4b-ui-backend
run_logged stage4b-ui-backend env RUST_LOG="${RUST_LOG:-error}" \
  SIMPLE_NO_DEPRECATED_WARNINGS=1 \
  LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_STUB_MISSING_RT=1 \
  SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
  "${full_bin}" native-build \
    --backend "${backend}" \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads "${jobs}" --cache-dir "${native_cache_dir}" \
  --mode "${bootstrap_mode}" --entry src/app/ui/main.spl \
  --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
  -o "${ui_backend_bin}"
[ -x "${ui_backend_bin}" ] || { echo "error: failed to compile cached UI backend" >&2; exit 1; }
echo "Full CLI binary: ${full_bin}"

# ===========================================================================
# Stage 5: Compile MCP servers (optional, skip with --no-mcp)
# ===========================================================================

mcp_build_ok=1
if [ "${build_mcp}" -eq 1 ]; then
  echo "Stage 5: compiling MCP servers..."

  # Build both servers before failing so both logs are available. The shared
  # fresh-artifact smoke below is the single fail-closed Stage 5 gate.
  mcp_stage=0
  for mcp_entry in "simple_mcp_server:src/app/mcp/main.spl" \
                    "simple_lsp_mcp_server:src/app/simple_lsp_mcp/main.spl"; do
    mcp_stage=$((mcp_stage + 1))
    mcp_name="${mcp_entry%%:*}"
    mcp_spl="${mcp_entry#*:}"
    mcp_log="stage5${mcp_stage}-mcp-native-build"

    echo "  Stage 5${mcp_stage}: ${mcp_name}"
    prepare_native_cache "stage5${mcp_stage}"
    rm -f "${full_dir}/${mcp_name}${exe_suffix}"
    set +e
    env RUST_LOG="${RUST_LOG:-error}" \
      SIMPLE_NO_DEPRECATED_WARNINGS=1 \
      LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
      SIMPLE_NO_STUB_FALLBACK=1 \
      SIMPLE_BINARY="$(absolute_path "${stage_for_build}")" \
      "${stage_for_build}" native-build \
      --backend "${backend}" \
      --source src/compiler --source src/app --source src/lib \
      --entry-closure \
      --threads "${jobs}" \
      --cache-dir "${native_cache_dir}" \
      --mode "${bootstrap_mode}" \
      --entry "${mcp_spl}" \
      --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
      -o "${full_dir}/${mcp_name}${exe_suffix}" \
      >"${log_dir}/${mcp_log}.log" 2>&1
    mcp_status=$?
    set -e
    echo "  ${mcp_log} log: ${log_dir}/${mcp_log}.log"
    if [ "${mcp_status}" -ne 0 ]; then
      mcp_build_ok=0
      echo "  WARNING: ${mcp_name} build failed (exit ${mcp_status})"
    elif [ ! -s "${full_dir}/${mcp_name}${exe_suffix}" ]; then
      mcp_build_ok=0
      echo "  WARNING: ${mcp_name} produced a zero-byte file"
    else
      printf '%s\n' "$(hash_file "${full_dir}/${mcp_name}${exe_suffix}")" \
        >"${full_dir}/${mcp_name}${exe_suffix}.sha256"
      echo "  ${mcp_name}: ${full_dir}/${mcp_name}${exe_suffix}"
    fi
  done

  if [ "${mcp_build_ok}" -ne 1 ]; then
    echo "error: Stage 5 MCP server build failed; refusing stale artifacts" >&2
    exit 1
  fi

  echo "Stage 5 smoke: fresh MCP initialize/list/call gate"
  if ! env \
    SIMPLE_BINARY="$(absolute_path "${full_bin}")" \
    MCP_SERVER="$(absolute_path "${full_dir}/simple_mcp_server${exe_suffix}")" \
    LSP_MCP_SERVER="$(absolute_path "${full_dir}/simple_lsp_mcp_server${exe_suffix}")" \
    MCP_NATIVE_BOOTSTRAP_FRESH=1 \
    sh scripts/check/check-mcp-native-smoke.shs; then
    echo "error: fresh Stage 5 MCP server smoke failed" >&2
    exit 1
  fi
else
  echo "Skipping MCP server builds (--no-mcp)"
fi

# ===========================================================================
# Deploy
# ===========================================================================

if [ "${deploy}" -eq 1 ]; then
  deploy_dir="bin/release/${PLATFORM}"
  mkdir -p "${deploy_dir}"

  # Deploy gate: never swap bin/simple to the self-hosted stage4 binary unless
  # a working seed driver exists at the delegate path. Without it the stage4
  # self-exec guard blocks `bin/simple test` host-wide (see
  # doc/08_tracking/bug/stage4_deploy_no_seed_test_runner_blocked_2026-06-11.md).
  seed_probe() {
    [ -x "$1" ] || return 1
    out="$(run_timeout 30 "$1" -c 'print(1+1)' 2>/dev/null)" || return 1
    [ "${out}" = "2" ]
  }
  seed_delegate="${deploy_dir}/simple_seed${exe_suffix}"
  seed_src="${full_dir}/simple_seed${exe_suffix}"
  if ! seed_probe "${seed_src}"; then
    echo "ERROR: deploy refused — current seed driver failed smoke test: ${seed_src}." >&2
    exit 1
  fi
  install -m755 "${seed_src}" "${seed_delegate}"
  echo "Installed current seed delegate: ${seed_src} -> ${seed_delegate}"

  deployed_bin="${deploy_dir}/simple${exe_suffix}"
  prev_bin="${deploy_dir}/simple${exe_suffix}.pre_deploy"
  [ -x "${deployed_bin}" ] && cp "${deployed_bin}" "${prev_bin}"
  install -m755 "${full_bin}" "${deployed_bin}"
  echo "Deployed full CLI binary to ${deployed_bin}"

  # Post-swap smoke: the deployed binary must evaluate code; restore on failure.
  smoke_out="$(run_timeout 30 "${deployed_bin}" -c 'print(1+1)' 2>/dev/null)"
  if [ "${smoke_out}" != "2" ]; then
    echo "ERROR: deployed binary failed smoke test (-c 'print(1+1)' -> '${smoke_out}')." >&2
    if [ -x "${prev_bin}" ]; then
      mv "${prev_bin}" "${deployed_bin}"
      echo "Restored previous binary to ${deployed_bin}" >&2
    fi
    exit 1
  fi
  rm -f "${prev_bin}"
  install -m755 "${ui_backend_bin}" "${deploy_dir}/simple_ui_backend${exe_suffix}"
  echo "Deployed cached UI backend to ${deploy_dir}/simple_ui_backend${exe_suffix}"

  # Deploy MCP servers if they were built successfully
  if [ "${build_mcp}" -eq 1 ] && [ "${mcp_build_ok}" -eq 1 ]; then
    for mcp_bin_name in simple_mcp_server simple_lsp_mcp_server; do
      if [ -x "${full_dir}/${mcp_bin_name}${exe_suffix}" ] && [ -s "${full_dir}/${mcp_bin_name}${exe_suffix}" ]; then
        mcp_deploy_tmp="${deploy_dir}/.${mcp_bin_name}${exe_suffix}.deploy.$$"
        mcp_hash_tmp="${deploy_dir}/.${mcp_bin_name}${exe_suffix}.sha256.deploy.$$"
        install -m755 "${full_dir}/${mcp_bin_name}${exe_suffix}" "${mcp_deploy_tmp}"
        install -m644 "${full_dir}/${mcp_bin_name}${exe_suffix}.sha256" "${mcp_hash_tmp}"
        mv "${mcp_deploy_tmp}" "${deploy_dir}/${mcp_bin_name}${exe_suffix}"
        mv "${mcp_hash_tmp}" "${deploy_dir}/${mcp_bin_name}${exe_suffix}.sha256"
        echo "Deployed ${mcp_bin_name} to ${deploy_dir}/${mcp_bin_name}${exe_suffix}"
      fi
    done
  fi

  # Recreate wrapper/launcher entrypoints (bin/simple plus release links)
  if [ "${os}" != "windows" ]; then
    "${repo_root}/scripts/setup/setup.shs"
  fi

  if [ "${release_tests}" -eq 1 ]; then
    echo "Stage 6: running release whole-test gate..."
    run_logged stage6-whole-tests "${deployed_bin}" test test --whole --mode=interpreter
  fi
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
