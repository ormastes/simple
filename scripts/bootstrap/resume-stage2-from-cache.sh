#!/bin/sh
# Resume Stage 2 in a fresh output through the canonical bootstrap while cloning
# its content-addressed native cache. This wrapper deliberately does not
# reproduce sanity, receiver, transcript, or admission-receipt logic: a second
# implementation of those contracts can silently certify a different command.
set -eu
umask 077

usage() {
    echo "usage: $0 OUTPUT_DIR" >&2
    exit 64
}

resume_fail() {
    echo "resume-stage2: refusal: $1" >&2
    exit 1
}

canonical_directory() {
    [ -d "$1" ] && [ ! -L "$1" ] || return 1
    resume_physical=$(CDPATH= cd -- "$1" && pwd -P) || return 1
    [ "$resume_physical" = "$1" ] || return 1
    printf '%s\n' "$resume_physical"
}

regular_file() {
    [ -f "$1" ] && [ ! -L "$1" ]
}

transcript_executable() {
    awk '
        /^executable:[0-9]+:/ {
            declared=$0
            sub(/^executable:/, "", declared)
            sub(/:.*/, "", declared)
            payload=$0
            sub(/^executable:[0-9]+:/, "", payload)
            if (length(payload) != declared) exit 2
            count++
            value=payload
        }
        END { if (count != 1) exit 1; print value }
    ' "$1"
}

transcript_explicit_env_names() {
    awk '
        /^explicit-env:[0-9]+:/ {
            declared=$0
            sub(/^explicit-env:/, "", declared)
            sub(/:.*/, "", declared)
            payload=$0
            sub(/^explicit-env:[0-9]+:/, "", payload)
            if (length(payload) != declared ||
                payload !~ /^[A-Z_][A-Z0-9_]*=/) exit 2
            name=payload
            sub(/=.*/, "", name)
            if (seen[name]++) exit 2
            names = names (names == "" ? "" : " ") name
        }
        END { if (names == "") exit 1; print names }
    ' "$1"
}

[ "$#" = 1 ] || usage
case "$1" in
    /*) ;;
    *) echo "resume-stage2: OUTPUT_DIR must be absolute" >&2; exit 64 ;;
esac
case "$1" in *'
'*) resume_fail "OUTPUT_DIR contains a newline" ;; esac

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
root=$(CDPATH= cd -- "$script_dir/../.." && pwd -P)
output=$(canonical_directory "$1") ||
    resume_fail "output directory is missing, symlinked, or non-canonical"
case "$output" in
    "$root"/build/*) ;;
    *) resume_fail "output directory must be below the worktree build directory" ;;
esac

facade="$root/scripts/check/lib/bootstrap-stage3-provenance.shs"
canonical_bootstrap="$root/scripts/bootstrap/bootstrap-from-scratch.sh"
regular_file "$facade" || resume_fail "Stage 3 provenance facade is missing"
regular_file "$canonical_bootstrap" || resume_fail "canonical bootstrap is missing"
BOOTSTRAP_STAGE3_FACADE_PATH=$facade
BOOTSTRAP_STAGE3_VERSION_ROOT=$root
export BOOTSTRAP_STAGE3_FACADE_PATH BOOTSTRAP_STAGE3_VERSION_ROOT
. "$facade"
PORTABLE_LOCK_ATOMIC_HELPER_PATH="$root/scripts/check/lib/portable-hardlink-lock.pl"
export PORTABLE_LOCK_ATOMIC_HELPER_PATH
. "$root/scripts/check/lib/portable-process-lock.shs"
. "$script_dir/stage2-cache-clone.shs"

# Use the canonical output lock while reading the prior run. A live bootstrap
# must not mutate its cache or transcript midway through validation/copying.
source_lock_root="$(dirname -- "$output")/.simple-bootstrap-locks"
source_lock_name="output-$(bootstrap_stage3_args_sha256 "$output")"
portable_lock_acquire "$source_lock_root" "$source_lock_name" 0 ||
    resume_fail "source output is owned by another bootstrap"
source_lock=$PORTABLE_LOCK_HANDLE
trap 'portable_lock_release "$source_lock"' EXIT
trap 'exit 1' HUP INT TERM

platform=$(bootstrap_stage3_host_platform) ||
    resume_fail "unsupported host platform"
stage2_dir="$output/stage2/$platform"
stage3_dir="$output/stage3/$platform"
cache="$stage3_dir/stage2-native-cache"
runtime="$stage3_dir/stage2-runtime-authority"
transcript="$stage3_dir/stage2-command.transcript"
canonical="$stage2_dir/simple"
admitted="$stage3_dir/stage2-admitted/simple"

canonical_directory "$stage2_dir" >/dev/null ||
    resume_fail "Stage 2 directory is missing, symlinked, or non-canonical"
canonical_directory "$stage3_dir" >/dev/null ||
    resume_fail "Stage 3 directory is missing, symlinked, or non-canonical"
canonical_directory "$cache" >/dev/null ||
    resume_fail "stage2-native-cache is missing, symlinked, or non-canonical"
canonical_directory "$runtime" >/dev/null ||
    resume_fail "stage2-runtime-authority is missing, symlinked, or non-canonical"
regular_file "$transcript" || resume_fail "Stage 2 command transcript is missing"
regular_file "$runtime/simple" || resume_fail "frozen runtime compiler is missing"
[ ! -e "$canonical" ] && [ ! -L "$canonical" ] ||
    resume_fail "canonical Stage 2 output already exists"
[ ! -e "$admitted" ] && [ ! -L "$admitted" ] ||
    resume_fail "an admitted Stage 2 output already exists"

# A cache resume is meaningful only when the prior run produced at least one
# content-addressed cache scope. Symlinks are not cache authority.
if find "$cache" -type l -print -quit | grep -q .; then
    resume_fail "stage2-native-cache contains a symlink"
fi
find "$cache" -type f -name .cache_scope -print -quit | grep -q . ||
    resume_fail "stage2-native-cache contains no completed scope"

target=$(bootstrap_stage3_transcript_argv_value_after "$transcript" --target) ||
    resume_fail "target missing from transcript"
backend=$(bootstrap_stage3_transcript_argv_value_after "$transcript" --backend) ||
    resume_fail "backend missing from transcript"
mode=$(bootstrap_stage3_transcript_argv_value_after "$transcript" --mode) ||
    resume_fail "mode missing from transcript"
threads=$(bootstrap_stage3_transcript_argv_value_after "$transcript" --threads) ||
    resume_fail "thread count missing from transcript"
transcript_cache=$(bootstrap_stage3_transcript_argv_value_after "$transcript" --cache-dir) ||
    resume_fail "cache path missing from transcript"
transcript_runtime=$(bootstrap_stage3_transcript_argv_value_after "$transcript" --runtime-path) ||
    resume_fail "runtime path missing from transcript"
transcript_output=$(bootstrap_stage3_transcript_argv_value_after "$transcript" -o) ||
    resume_fail "output path missing from transcript"
transcript_bundle=$(bootstrap_stage3_transcript_argv_value_after "$transcript" --runtime-bundle) ||
    resume_fail "runtime bundle missing from transcript"
transcript_entry=$(bootstrap_stage3_transcript_argv_value_after "$transcript" --entry) ||
    resume_fail "entry missing from transcript"

[ "$target" = "$platform" ] || resume_fail "target differs from the host"
[ "$backend" = llvm ] || resume_fail "only the canonical LLVM Stage 2 lane is resumable"
[ "$mode" = dynload ] || resume_fail "only the canonical dynload lane is resumable"
case "$threads" in ''|*[!0-9]*|0) resume_fail "invalid transcript thread count" ;; esac
[ "$transcript_cache" = "$cache" ] || resume_fail "transcript cache path is not canonical"
[ "$transcript_runtime" = "$runtime" ] || resume_fail "transcript runtime path is not canonical"
[ "$transcript_output" = "$canonical" ] || resume_fail "transcript output path is not canonical"
[ "$transcript_bundle" = core-c-bootstrap ] || resume_fail "runtime bundle is not canonical"
[ "$transcript_entry" = src/app/cli/bootstrap_main.spl ] ||
    resume_fail "entry is not bootstrap_main"
[ "$(transcript_executable "$transcript")" = "$runtime/simple" ] ||
    resume_fail "transcript executable is not the frozen runtime compiler"

expected_env_names=$(bootstrap_stage3_stage2_canonical_env_names "$platform") ||
    resume_fail "canonical environment set is unavailable"
[ "$(transcript_explicit_env_names "$transcript")" = "$expected_env_names" ] ||
    resume_fail "transcript environment set is not canonical"

SIMPLE_ABI_POLICY=$(bootstrap_stage3_transcript_explicit_env_value "$transcript" SIMPLE_ABI_POLICY) ||
    resume_fail "ABI policy missing from transcript"
SIMPLE_PLUGIN_MANIFEST_POLICY=$(bootstrap_stage3_transcript_explicit_env_value "$transcript" SIMPLE_PLUGIN_MANIFEST_POLICY) ||
    resume_fail "plugin policy missing from transcript"
SIMPLE_KERNEL_K1_POLICY=$(bootstrap_stage3_transcript_explicit_env_value "$transcript" SIMPLE_KERNEL_K1_POLICY) ||
    resume_fail "K1 policy missing from transcript"
SIMPLE_COVERAGE_CUTOVER_STATE=$(bootstrap_stage3_transcript_explicit_env_value "$transcript" SIMPLE_COVERAGE_CUTOVER_STATE) ||
    resume_fail "coverage policy missing from transcript"
[ "$SIMPLE_ABI_POLICY" = v1 ] || resume_fail "ABI policy is not canonical"
[ "$SIMPLE_PLUGIN_MANIFEST_POLICY" = simple-sdn ] || resume_fail "plugin policy is not canonical"
[ "$SIMPLE_KERNEL_K1_POLICY" = llvm-cranelift ] || resume_fail "K1 policy is not canonical"
[ "$SIMPLE_COVERAGE_CUTOVER_STATE" = atomic-apk-only ] ||
    resume_fail "coverage policy is not canonical"
export SIMPLE_ABI_POLICY SIMPLE_PLUGIN_MANIFEST_POLICY
export SIMPLE_KERNEL_K1_POLICY SIMPLE_COVERAGE_CUTOVER_STATE

path_value=$(bootstrap_stage3_transcript_host_value "$transcript" PATH) ||
    resume_fail "PATH is missing from transcript"
case "$path_value" in /*) ;; *) resume_fail "transcript PATH is not absolute" ;; esac
printf '%s\n' "$path_value" | grep -Eq '(^|:)([^/]|$)' &&
    resume_fail "transcript PATH contains a non-absolute entry"
PATH=$path_value
export PATH

# Match the canonical bootstrap's non-overridable 10 GiB start floor. The
# delegated entrypoint repeats its own check after it has acquired ownership.
free_kib=$(df -Pk "$output" 2>/dev/null | awk 'END { print $4 }') ||
    resume_fail "free-space query failed"
case "$free_kib" in ''|*[!0-9]*) resume_fail "free-space query was invalid" ;; esac
[ "$free_kib" -ge 10485760 ] ||
    resume_fail "fewer than 10 GiB are free on the output filesystem"

# Only native cache files cross into the new output. Old sanity evidence,
# transcripts, runtime snapshots and rejected/admitted binaries stay behind.
bootstrap_stage2_clone_cache "$cache" "$root/build" \
    "$platform" "$source_lock" || resume_fail "native cache clone failed"
fresh_output=$BOOTSTRAP_STAGE2_CLONE_OUTPUT
portable_lock_release "$source_lock" || resume_fail "source lock release failed"
trap - EXIT HUP INT TERM
printf 'resume-stage2: fresh output: %s\n' "$fresh_output"

# The canonical entrypoint owns cache locking, fresh pre/post snapshots,
# transcribed execution, candidate hash stability, runtime/receiver checks,
# immutable private admission, and parent-receipt publication. It preserves
# content-addressed Stage 2 cache scopes unless explicitly passed --fresh-cache;
# this wrapper never passes that option.
exec sh "$canonical_bootstrap" --full-bootstrap --backend="$backend" \
    --mode="$mode" --jobs="$threads" --stop-after-stage2 --output="$fresh_output"
