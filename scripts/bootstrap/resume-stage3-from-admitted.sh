#!/bin/sh
set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)
source_output=${1:?usage: resume-stage3-from-admitted.sh OUTPUT_DIR}
platform=aarch64-apple-darwin
source_stage3="$root/$source_output/stage3/$platform"
admitted="$source_stage3/stage2-admitted/simple"
runtime="$source_stage3/stage2-runtime-authority"
stage2_sanity="$source_stage3/stage2-sanity.env"
lane="$source_stage3/recovery-threads1"
candidate="$lane/simple"
transcript="$lane/stage3-command.transcript"
log="$lane/stage3-native-build.log"
home="$lane/home"
tmp="$lane/tmp"
cache="$lane/cache"
lock="$lane/lock"
path=${PATH:?PATH is required}

BOOTSTRAP_STAGE3_FACADE_PATH="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
export BOOTSTRAP_STAGE3_FACADE_PATH
. "$BOOTSTRAP_STAGE3_FACADE_PATH"

mkdir -p "$lane" "$home" "$tmp" "$cache" "$lock"
printf '%s\n' "$$" >"$lock/pid"
[ -x "$admitted" ] && [ -d "$runtime" ] && [ -f "$stage2_sanity" ] || exit 1
admitted_sha=$(bootstrap_stage3_hash_file "$admitted")
[ "$admitted_sha" = 60e48b27d0c7cbd0983d502c70ca8becb4aedd1f58038ce3358b4173949cbf0a ] || exit 1
[ "$(bootstrap_stage3_manifest_value status "$stage2_sanity")" = pass ] || exit 1
[ "$(bootstrap_stage3_manifest_value candidate_sha256_after "$stage2_sanity")" = "$admitted_sha" ] || exit 1

bootstrap_stage3_source_snapshot "$lane/source-before.txt" "$root"
bootstrap_stage3_git_state "$root" "$lane/git-before.env"
bootstrap_stage3_tool_authority_snapshot "$lane/tools-before.txt" "$path" "$root"
bootstrap_stage3_directory_snapshot "$lane/runtime-before.txt" "$runtime"
rm -f "$candidate" "$log" "$transcript"

set +e
bootstrap_stage3_run_transcribed "$transcript" "$root" "$log" "$home" "$tmp" "$path" \
  RUST_LOG=error LIBRARY_PATH= SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256=absent \
  SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_NATIVE_ARENA_DECLS=1 \
  SIMPLE_NO_STUB_FALLBACK=1 LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  SIMPLE_NATIVE_BUILD_TARGET="$platform" SIMPLE_NATIVE_BUILD_THREADS=1 \
  SIMPLE_NATIVE_BUILD_CACHE_DIR="$cache" SIMPLE_RUNTIME_PATH="$runtime" \
  SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c-bootstrap SIMPLE_BINARY="$admitted" -- \
  "$admitted" native-build --target "$platform" --backend cranelift \
  --runtime-bundle core-c-bootstrap --threads 1 --cache-dir "$cache" \
  --mode dynload --runtime-path "$runtime" -o "$candidate" \
  src/app/cli/bootstrap_main.spl
status=$?
set -e
[ "$status" -eq 0 ] && [ -x "$candidate" ] || exit "$status"
! grep -qE '^(Build complete: [0-9]+ compiled|Linked: .* via clang)' "$log" || exit 1
[ "$(bootstrap_stage3_hash_file "$admitted")" = "$admitted_sha" ] || exit 1

bootstrap_stage3_source_snapshot "$lane/source-after.txt" "$root"
bootstrap_stage3_git_state "$root" "$lane/git-after.env"
bootstrap_stage3_tool_authority_snapshot "$lane/tools-after.txt" "$path" "$root"
bootstrap_stage3_directory_snapshot "$lane/runtime-after.txt" "$runtime"
cmp -s "$lane/source-before.txt" "$lane/source-after.txt"
cmp -s "$lane/git-before.env" "$lane/git-after.env"
cmp -s "$lane/tools-before.txt" "$lane/tools-after.txt"
cmp -s "$lane/runtime-before.txt" "$lane/runtime-after.txt"

version=$($candidate --version)
[ "$version" = "simple-bootstrap 1.0.0-beta" ]
unsupported_status=0
unsupported=$($candidate run scripts/check/cert/redeploy_gate/fixtures/p2_add.spl 2>&1) || unsupported_status=$?
[ "$unsupported_status" -eq 1 ]
case "$unsupported" in *"unknown command 'run'"*) ;; *) exit 1 ;; esac

candidate_sha=$(bootstrap_stage3_hash_file "$candidate")
{
  echo schema=simple-bootstrap-stage3-recovery-v1
  echo status=pass
  echo stage2_admitted_sha256="$admitted_sha"
  echo stage3_sha256="$candidate_sha"
  echo stage3_threads=1
  echo stage3_transcript_sha256="$(bootstrap_stage3_hash_file "$transcript")"
  echo stage3_log_sha256="$(bootstrap_stage3_hash_file "$log")"
  echo source_snapshot_sha256="$(bootstrap_stage3_hash_file "$lane/source-after.txt")"
  echo git_snapshot_sha256="$(bootstrap_stage3_hash_file "$lane/git-after.env")"
  echo tool_snapshot_sha256="$(bootstrap_stage3_hash_file "$lane/tools-after.txt")"
  echo runtime_snapshot_sha256="$(bootstrap_stage3_hash_file "$lane/runtime-after.txt")"
} >"$lane/recovery-provenance.env"
echo "Stage 3 recovery admitted: $candidate"
echo "SHA-256: $candidate_sha"
