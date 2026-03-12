#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/bootstrap-from-scratch.sh [options]

Linux bootstrap wrapper for the verified staged bootstrap pipeline.

Options:
  --backend=<name>   Backend for stage2/stage3 (default: llvm-lib)
  --output=<dir>     Output directory for bootstrap artifacts (default: bootstrap)
  --deploy           Copy the verified stage3 binary to bin/release/simple
  --keep-artifacts   Accepted for compatibility; bootstrap artifacts are kept
  --no-verify        Accepted for compatibility; hash verification still runs
  --help             Show this help
EOF
}

backend="llvm-lib"
output_dir="bootstrap"
deploy=0

while (($#)); do
  case "$1" in
    --backend=*)
      backend="${1#*=}"
      ;;
    --output=*)
      output_dir="${1#*=}"
      ;;
    --deploy)
      deploy=1
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

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
cd "${repo_root}"

seed_bin="src/compiler_rust/target/bootstrap/simple"

if [[ ! -x "${seed_bin}" ]]; then
  echo "Building Rust seed compiler..."
  cargo build --manifest-path src/compiler_rust/Cargo.toml --profile bootstrap -p simple-driver
fi

if [[ ! -x "bin/release/simple" ]]; then
  echo "error: bin/release/simple is required for the staged bootstrap wrapper in this checkout" >&2
  exit 1
fi

echo "Running Linux bootstrap pipeline..."
echo "  backend: ${backend}"
echo "  output:  ${output_dir}"

RUST_LOG="${RUST_LOG:-error}" \
  bin/release/simple build bootstrap "--backend=${backend}" "--output=${output_dir}"

stage2="${output_dir}/simple_stage2"
stage3="${output_dir}/simple_stage3"

if [[ ! -x "${stage2}" || ! -x "${stage3}" ]]; then
  echo "error: expected bootstrap artifacts were not produced" >&2
  exit 1
fi

hash2="$(sha256sum "${stage2}" | awk '{print $1}')"
hash3="$(sha256sum "${stage3}" | awk '{print $1}')"

echo "stage2 sha256: ${hash2}"
echo "stage3 sha256: ${hash3}"

if [[ "${hash2}" != "${hash3}" ]]; then
  echo "error: stage2 and stage3 hashes differ" >&2
  exit 1
fi

if (( deploy )); then
  install -Dm755 "${stage3}" "bin/release/simple"
  echo "Deployed verified binary to bin/release/simple"
fi

echo "Bootstrap verification passed."
