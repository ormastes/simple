#!/bin/sh
set -eu

usage() {
  cat <<'EOF'
Usage: scripts/bootstrap/bootstrap-freebsd-seed.sh [options]

FreeBSD seed bootstrap verifier.

This flow verifies the checked-in FreeBSD seed compiler by:
1. copying bin/freebsd/simple to bin/simple
2. transpiling the same smoke test twice and checking deterministic output
3. normalizing the generated C++ entry point
4. compiling and running the smoke binary with the FreeBSD runtime objects

Options:
  --output=<dir>     Output directory for artifacts (default: bootstrap)
  --deploy           Accepted for compatibility; bin/simple is installed either way
  --verbose          Accepted for compatibility
  --jobs=<n>         Accepted for compatibility
  --help             Show this help
EOF
}

output_dir="bootstrap"

while [ "$#" -gt 0 ]; do
  case "$1" in
    --output=*)
      output_dir=${1#*=}
      ;;
    --deploy|--verbose)
      ;;
    --jobs=*)
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

if [ "$(uname -s 2>/dev/null || echo unknown)" != "FreeBSD" ]; then
  echo "error: FreeBSD seed bootstrap must run on FreeBSD" >&2
  exit 1
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "${script_dir}/../.." && pwd)
cd "${repo_root}"

if [ ! -x "bin/freebsd/simple" ]; then
  echo "error: bin/freebsd/simple not found" >&2
  exit 1
fi

if ! command -v clang >/dev/null 2>&1; then
  echo "error: clang not found" >&2
  exit 1
fi

if ! command -v clang++ >/dev/null 2>&1; then
  echo "error: clang++ not found" >&2
  exit 1
fi

hash_cmd() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    sha256 -q "$1"
  fi
}

mkdir -p "${output_dir}"
mkdir -p "${output_dir}/runtime"
rm -f bin/simple
cp bin/freebsd/simple bin/simple
chmod +x bin/simple

smoke_spl="${output_dir}/freebsd_seed_smoke.spl"
stage1_cpp="${output_dir}/freebsd_seed_stage1.cpp"
stage2_cpp="${output_dir}/freebsd_seed_stage2.cpp"
norm_cpp="${output_dir}/freebsd_seed_stage1.norm.cpp"
runtime_dir="${output_dir}/runtime"
smoke_bin="${output_dir}/freebsd_seed_smoke"

cat > "${smoke_spl}" <<'EOF'
fn main():
    print "freebsd seed ok"
EOF

echo "Running FreeBSD seed bootstrap verifier..."
echo "  output:  ${output_dir}"

bin/freebsd/simple "${smoke_spl}" > "${stage1_cpp}"
bin/freebsd/simple "${smoke_spl}" > "${stage2_cpp}"

hash1=$(hash_cmd "${stage1_cpp}")
hash2=$(hash_cmd "${stage2_cpp}")
echo "stage1 cpp sha256: ${hash1}"
echo "stage2 cpp sha256: ${hash2}"

if [ "${hash1}" != "${hash2}" ]; then
  echo "error: repeated seed transpilation is not deterministic" >&2
  exit 1
fi

awk '
/^void main\(\);$/ { print "void spl_main();"; next }
/^void main\(\) \{$/ { print "void spl_main() {"; next }
{
  print $0
  if ($0 == "    __module_init();") {
    print "    spl_main();"
  }
}
' "${stage1_cpp}" > "${norm_cpp}"

clang -c -I"${repo_root}/src/runtime" "${repo_root}/src/runtime/runtime.c" -o "${runtime_dir}/runtime.o"
clang -c -I"${repo_root}/src/runtime" "${repo_root}/src/runtime/runtime_memtrack.c" -o "${runtime_dir}/runtime_memtrack.o"
clang -c -I"${repo_root}/src/runtime" "${repo_root}/src/runtime/runtime_native.c" -o "${runtime_dir}/runtime_native.o"
clang -c -I"${repo_root}/src/runtime" "${repo_root}/src/runtime/runtime_thread.c" -o "${runtime_dir}/runtime_thread.o"
clang -c -I"${repo_root}/src/runtime" "${repo_root}/src/runtime/async_driver.c" -o "${runtime_dir}/async_driver.o"
clang -c -I"${repo_root}/src/runtime" "${repo_root}/src/runtime/runtime_fork.c" -o "${runtime_dir}/runtime_fork.o"
clang -c -I"${repo_root}/src/runtime" "${repo_root}/src/runtime/platform/async_freebsd.c" -o "${runtime_dir}/async_freebsd.o"

clang++ -std=c++20 -pthread -I"${repo_root}/src/runtime" \
  "${norm_cpp}" \
  "${runtime_dir}/runtime.o" \
  "${runtime_dir}/runtime_memtrack.o" \
  "${runtime_dir}/runtime_native.o" \
  "${runtime_dir}/runtime_thread.o" \
  "${runtime_dir}/async_driver.o" \
  "${runtime_dir}/runtime_fork.o" \
  "${runtime_dir}/async_freebsd.o" \
  -o "${smoke_bin}"

smoke_output=$("${smoke_bin}")
echo "${smoke_output}"
if [ "${smoke_output}" != "freebsd seed ok" ]; then
  echo "error: smoke binary output mismatch" >&2
  exit 1
fi

file bin/simple
echo "Bootstrap verification passed."
