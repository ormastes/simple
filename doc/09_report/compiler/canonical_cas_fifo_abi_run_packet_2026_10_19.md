# Bounded FIFO ABI execution packet — 2026-10-19

**AUTHORED / UNRUN.** Exact reviewed source commit:
`aa5cb90ddbbd98f0acf304af4bba16c81b6c2184` (`ACCEPT_STATIC`, parent/reviewer
binding). This packet does not change that source or claim executed evidence.
The [provider bug report](../../08_tracking/bug/bounded_regular_read_fifo_open_2026_10_19.md)
describes the behavior; the [combined report](canonical_cas_fifo_qualification_2026_10_19.md)
owns qualification. Simple CAS11 remains UNRUN independently of this C test.

## Scope and dependency closure

Run only on GNU/Linux with Bash, a native GNU-compatible C compiler, GNU ld,
objcopy, nm, Git, tar, coreutils (including timeout/sha256sum), awk, and
`/usr/bin/time`. System development dependencies are libc headers/linker startup
objects, Linux UAPI headers, pthread, libdl and libm; there is no Cargo, Rust seed,
OpenSSL, mimalloc, runtime archive, compiler backfill, or Simple binary dependency.
Do not define `SIMPLE_RUNTIME_MEMORY_OWNER`, `SPL_HAVE_OPENSSL`, or `USE_MIMALLOC`.
This is the isolated hosted-C provider configuration used by the existing
`scripts/check/check-runtime-concat-nul.shs` and
`scripts/check/check-cli-provider-v1-host.shs` conventions, not a qualification
of a different memory-owner configuration or a running compiler executable.

The native probe links the complete compiled `runtime_native.c` object; its
bounded reader, text/byte constructors and accessors are in that translation
unit. Final section garbage collection discards unrelated runtime entry points.
Compatibility uses the complete compiled `runtime.c` object. Its text constructor
and accessor dependencies come from the same real native object, retained by
relocation reachability from three explicit string roots using `ld -r
--gc-sections`. This object operation has an in-repo precedent in
`scripts/bootstrap/repair-linux-bootstrap-runtime.shs:39`. No source function is
copied/extracted, symbol renamed, stub supplied, or duplicate definition allowed.
The support object must export exactly those three roots and no bounded-reader
symbol. Link traces and maps must attribute compatibility reader/diagnostic
definitions to `runtime.o`. Failure is a stop, not permission to relax linkage.

The manifest below contains both production translation units, the actual test,
and all 28 recursively quoted in-tree headers (including inactive platform
branches). The only unresolved quoted include is opt-in `mimalloc.h`, excluded by
configuration. Native memory/string/byte reachable calls need no additional
production C translation units by source inspection. Successful compilation and
linking are still required evidence; this source analysis is not a link PASS.

## Limits and evidence

One command at a time. Each build/link step has 120 seconds wall time, 90 seconds
CPU per process, and 1 GiB address-space ceiling. Each executable gets 60 seconds
wall time, 30 seconds CPU per process, and 256 MiB address-space ceiling. Core
dumps are disabled. GNU timeout sends TERM, then KILL after two seconds; the test
also has its own child alarm and parent kill/reap deadlines. These are chosen
limits, **not measured resource estimates**. Full translation-unit compilation
cost is unknown. Exceeding a ceiling means blocked qualification; stop and report.
No parallel compile, retry loop, shared artifact update, or green-check replay.

The packet creates one fresh mode-0700 `/tmp/simple-fifo-abi-aa5cb90.*` root.
It snapshots only the listed files from the immutable commit, records compiler
and linker versions, source/archive/object/executable hashes, compiler dependency
files, exact shell-quoted commands, timing, exit status, stdout/stderr, symbol
tables and link maps. Keep this directory as evidence. Test fixtures live solely
under its `fixtures` child and are removed by the selfcheck on ordinary completion.
An externally killed test may leave fixtures only inside this owned directory.

## 1. Prepare pinned source and bounded command runner

Execute this block once in Bash. The remaining blocks run in the same shell.
The worktree is read only; no index, tracked source, livecache or source439 write
occurs. `$FIFO_CC` names one native compiler executable, not a shell command.

```bash
set -euo pipefail
FIFO_REPO=/home/yoon/dev/simple-phase3-loader-memory-astra-20261013
FIFO_REV=aa5cb90ddbbd98f0acf304af4bba16c81b6c2184
FIFO_CC=cc
FIFO_OUT=$(mktemp -d /tmp/simple-fifo-abi-aa5cb90.XXXXXX)
FIFO_SRC="$FIFO_OUT/source"
mkdir "$FIFO_SRC" "$FIFO_OUT/fixtures"
printf '%s\n' "$FIFO_OUT"
test "$(git -C "$FIFO_REPO" rev-parse --verify "$FIFO_REV^{commit}")" = "$FIFO_REV"
printf '%s\n' "$FIFO_REV" > "$FIFO_OUT/source.commit"
FIFO_SOURCES=(
  src/runtime/runtime.c
  src/runtime/runtime_native.c
  src/runtime/test/rt_bounded_read_fifo_selfcheck.c
  src/runtime/runtime.h
  src/runtime/runtime_any_ops.h
  src/runtime/runtime_collection_capture_impl.h
  src/runtime/runtime_core_intrinsics_impl.h
  src/runtime/runtime_fd_stat_v1.h
  src/runtime/runtime_fork.h
  src/runtime/runtime_memory_guard.h
  src/runtime/runtime_memtrack.h
  src/runtime/runtime_shared_parse_cell_private.h
  src/runtime/runtime_simd_dispatch.h
  src/runtime/runtime_sosix_directory_roots_v1.h
  src/runtime/runtime_startup_args.h
  src/runtime/runtime_string_ffi.h
  src/runtime/runtime_thread.h
  src/runtime/simple_gui_event_provider_abi_v1.h
  src/runtime/simple_gui_html_provider_abi_v1.h
  src/runtime/platform/platform.h
  src/runtime/platform/platform_freebsd.h
  src/runtime/platform/platform_linux.h
  src/runtime/platform/platform_macos.h
  src/runtime/platform/platform_netbsd.h
  src/runtime/platform/platform_openbsd.h
  src/runtime/platform/platform_win.h
  src/runtime/platform/runtime_group_self_charge.h
  src/runtime/platform/runtime_win_long_path.h
  src/runtime/platform/unix_common.h
  src/runtime/platform/windows_command_line_private.h
  src/runtime/platform/windows_raw_mapping.h
)
printf '%s\n' "${FIFO_SOURCES[@]}" > "$FIFO_OUT/source.manifest"
git -C "$FIFO_REPO" archive --format=tar "$FIFO_REV" -- "${FIFO_SOURCES[@]}" \
  > "$FIFO_OUT/source.tar"
tar -xf "$FIFO_OUT/source.tar" -C "$FIFO_SRC"
(cd "$FIFO_SRC" && sha256sum "${FIFO_SOURCES[@]}") > "$FIFO_OUT/source.sha256"
sha256sum "$FIFO_OUT/source.tar" > "$FIFO_OUT/archive.sha256"
cat > "$FIFO_OUT/reviewed.sha256" <<'SHA256'
901fb7e488c44e3c20b60167fb3557fd0d9c8fb7395396412124303faf351e64  src/runtime/runtime_native.c
47c179de72f68c2fa16de1c63f9039e96853a99664ca0a1dedb9f4ce4e63d6cc  src/runtime/runtime.c
aed2b1d12eb8187ee0aec63b7b503ff4b6fde8f701d71577afbec6fb855edb6f  src/runtime/test/rt_bounded_read_fifo_selfcheck.c
SHA256
(cd "$FIFO_SRC" && sha256sum -c "$FIFO_OUT/reviewed.sha256") \
  > "$FIFO_OUT/reviewed-hash-check.log"
{
  uname -srm
  command -v "$FIFO_CC" ld objcopy nm timeout
  "$FIFO_CC" --version
  "$FIFO_CC" -dumpmachine
  ld --version
  objcopy --version
} > "$FIFO_OUT/toolchain.txt"

fifo_bounded() (
  label=$1; seconds=$2; memory_kib=$3; cpu_seconds=$4; shift 4
  ulimit -c 0
  ulimit -v "$memory_kib"
  ulimit -t "$cpu_seconds"
  printf '%q ' "$@" > "$FIFO_OUT/$label.command"
  printf '\n' >> "$FIFO_OUT/$label.command"
  result=0
  /usr/bin/time -v -o "$FIFO_OUT/$label.time" \
    timeout --signal=TERM --kill-after=2s "${seconds}s" "$@" \
    > "$FIFO_OUT/$label.stdout" 2> "$FIFO_OUT/$label.stderr" || result=$?
  printf '%s\n' "$result" > "$FIFO_OUT/$label.exit"
  printf '%s exit=%s\n' "$label" "$result"
  exit "$result"
)
FIFO_PROVIDER_FLAGS=(-x c -std=gnu11 -O1 -g0 -fno-lto -pthread -D_GNU_SOURCE
  -ffunction-sections -fdata-sections -I"$FIFO_SRC/src/runtime")
FIFO_TEST_FLAGS=(-std=c11 -O2 -g0 -Wall -Wextra -Werror)
```

## 2. Native provider: actual text and bytes ABI

```bash
fifo_bounded native-compile 120 1048576 90 "$FIFO_CC" "${FIFO_PROVIDER_FLAGS[@]}" \
  -MMD -MF "$FIFO_OUT/native.d" -c "$FIFO_SRC/src/runtime/runtime_native.c" \
  -o "$FIFO_OUT/runtime_native.o"
fifo_bounded native-test-compile 120 1048576 90 "$FIFO_CC" "${FIFO_TEST_FLAGS[@]}" \
  -c "$FIFO_SRC/src/runtime/test/rt_bounded_read_fifo_selfcheck.c" \
  -o "$FIFO_OUT/native-probe.o"
fifo_bounded native-link 120 1048576 90 "$FIFO_CC" -fno-lto -pthread \
  "$FIFO_OUT/native-probe.o" "$FIFO_OUT/runtime_native.o" \
  -Wl,--gc-sections,-Map,"$FIFO_OUT/native.map" \
  -Wl,--trace-symbol=rt_file_read_regular_no_follow_bounded \
  -Wl,--trace-symbol=rt_file_read_regular_no_follow_bounded_bytes \
  -Wl,--trace-symbol=rt_file_read_regular_no_follow_last_failure \
  -ldl -lm -o "$FIFO_OUT/native-probe"
for symbol in rt_file_read_regular_no_follow_bounded \
  rt_file_read_regular_no_follow_bounded_bytes rt_file_read_regular_no_follow_last_failure; do
  grep -F "$FIFO_OUT/runtime_native.o: definition of $symbol" "$FIFO_OUT/native-link.stderr"
done
nm -g --defined-only "$FIFO_OUT/native-probe" > "$FIFO_OUT/native.symbols"
sha256sum "$FIFO_OUT/runtime_native.o" "$FIFO_OUT/native-probe.o" \
  "$FIFO_OUT/native-probe" > "$FIFO_OUT/native-artifacts.sha256"
fifo_bounded native-run 60 262144 30 "$FIFO_OUT/native-probe" "$FIFO_OUT/fixtures"
grep -Fx 'PASS bounded FIFO provider contract: 14/14 cases' "$FIFO_OUT/native-run.stdout"
```

Acceptance requires successful compilation/link/hash/symbol checks, run exit 0,
and the exact 14/14 summary. A missing symbol or unavailable header is a blocked
test, never a skip/pass. The provider's ordinary warnings are retained; harness
warnings are errors. Do not claim full compiler/runtime qualification from this
isolated default hosted-C configuration.

## 3. Compatibility provider: actual text ABI

This reuses the already compiled native object; it does not rerun the native test.
The support object retains the production string registry/allocation closure.
`objcopy --strip-unneeded` removes unused symbol-table entries left by partial
linking, as in the existing repair convention; it does not substitute code.

```bash
fifo_bounded string-support-link 120 1048576 90 ld -r --gc-sections \
  --undefined=rt_string_new --undefined=rt_string_len --undefined=rt_string_data \
  "$FIFO_OUT/runtime_native.o" -Map "$FIFO_OUT/native-string-support.map" \
  -o "$FIFO_OUT/native-string-support.o"
fifo_bounded string-support-strip 120 1048576 90 objcopy --strip-unneeded \
  "$FIFO_OUT/native-string-support.o"
nm -g --defined-only "$FIFO_OUT/native-string-support.o" > "$FIFO_OUT/string-support.symbols"
awk 'NF >= 2 {print $NF}' "$FIFO_OUT/string-support.symbols" | LC_ALL=C sort \
  > "$FIFO_OUT/string-support.actual"
printf '%s\n' rt_string_data rt_string_len rt_string_new > "$FIFO_OUT/string-support.expected"
diff -u "$FIFO_OUT/string-support.expected" "$FIFO_OUT/string-support.actual"
nm --defined-only "$FIFO_OUT/native-string-support.o" > "$FIFO_OUT/string-support.all-symbols"
if grep -E 'rt_(file_read_regular_no_follow|read_regular_no_follow_buffer)' \
  "$FIFO_OUT/string-support.all-symbols"; then
  printf 'REFUSE: native bounded-reader definition survived string support collection\n' >&2
  exit 1
fi
fifo_bounded compat-compile 120 1048576 90 "$FIFO_CC" "${FIFO_PROVIDER_FLAGS[@]}" \
  -MMD -MF "$FIFO_OUT/compat.d" -c "$FIFO_SRC/src/runtime/runtime.c" \
  -o "$FIFO_OUT/runtime.o"
fifo_bounded compat-test-compile 120 1048576 90 "$FIFO_CC" "${FIFO_TEST_FLAGS[@]}" \
  -DTEXT_ONLY -c "$FIFO_SRC/src/runtime/test/rt_bounded_read_fifo_selfcheck.c" \
  -o "$FIFO_OUT/compat-probe.o"
fifo_bounded compat-link 120 1048576 90 "$FIFO_CC" -fno-lto -pthread \
  "$FIFO_OUT/compat-probe.o" "$FIFO_OUT/runtime.o" "$FIFO_OUT/native-string-support.o" \
  -Wl,--gc-sections,-Map,"$FIFO_OUT/compat.map" \
  -Wl,--trace-symbol=rt_file_read_regular_no_follow_bounded \
  -Wl,--trace-symbol=rt_file_read_regular_no_follow_last_failure \
  -Wl,--trace-symbol=rt_string_new -ldl -lm -o "$FIFO_OUT/compat-probe"
for symbol in rt_file_read_regular_no_follow_bounded rt_file_read_regular_no_follow_last_failure; do
  grep -F "$FIFO_OUT/runtime.o: definition of $symbol" "$FIFO_OUT/compat-link.stderr"
done
grep -F "$FIFO_OUT/native-string-support.o: definition of rt_string_new" "$FIFO_OUT/compat-link.stderr"
nm -g --defined-only "$FIFO_OUT/compat-probe" > "$FIFO_OUT/compat.symbols"
sha256sum "$FIFO_OUT/native-string-support.o" "$FIFO_OUT/runtime.o" \
  "$FIFO_OUT/compat-probe.o" "$FIFO_OUT/compat-probe" > "$FIFO_OUT/compat-artifacts.sha256"
fifo_bounded compat-run 60 262144 30 "$FIFO_OUT/compat-probe" "$FIFO_OUT/fixtures"
grep -Fx 'PASS bounded FIFO provider contract: 7/7 cases' "$FIFO_OUT/compat-run.stdout"
```

Acceptance requires all checks above, exit 0 and 7/7. This independently qualifies
`runtime.c`'s actual bounded reader with the stated real native string support;
it does not assert that the C++ project-build runtime configuration is globally
complete. Keep every `.map`, symbol table and hash with the run logs.

## Reporting and stop criteria

Record each lane separately as PASS, FAIL, or BLOCKED with exact exit/status and
logs. Read timing files for observed resource use. Stop after the single candidate
run per lane. Old-provider baseline execution, Rust-provider tests, Simple CAS11,
source439 relink, and broader suites are outside this packet; do not infer their
status from these runs. If a dependency/compiler/linker problem occurs, report the
concrete failure before any repair; no speculative source edits or repeat loops.
