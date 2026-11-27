# Docker Cross-Language Profile Native Link Blocker

Status: STALE 2026-11-11 (lane ne6) — the June premise (checked-in single
release wrapper + in-container glibc `__tls_get_addr` link failure) describes an
artifact layout measured gone on 2026-09-13; the link-order fix survives in
source; docker is unavailable on the triage host. Falsifiable re-run grant in
the addendum.

## Status

Partially fixed. Rebuilt release-wrapper profile runs have passed in Docker, but
the debug compiler path `src/compiler_rust/target/debug/simple` still
reproduces the native linker failure inside the container. The checked-in
`bin/release/simple` wrapper is currently a separate stale-artifact blocker and
must not be treated as equivalent to a freshly rebuilt release wrapper.

## Summary

`PROFILE_DOCKER_ISOLATION=1` with `simple-cross-language-perf:latest` runs the
existing cross-language profile script in a separate Docker process with C and
Go toolchains available. A freshly rebuilt release-wrapper compiler path
supports contract-gated Simple native rows inside the container, but the debug
compiler path still fails during native linking. The checked-in release wrapper
currently points at a missing platform binary; that stale-wrapper state is
tracked separately in
`doc/08_tracking/bug/multicore_green_release_binary_stale_2026-06-11.md`.

## Evidence

Command:

```sh
PROFILE_DOCKER_ISOLATION=1 RUNS=1 WARM_IN_PROCESS=1 CPU_WORKERS=1 \
OS_THREAD_WORKERS=1 MULTICORE_GREEN_WORKERS=1 COOPERATIVE_GREEN_WORKERS=1 \
FANOUT_WORKERS=2 FANOUT_MULTICORE_GREEN_WORKERS=2 \
FANOUT_COOPERATIVE_GREEN_WORKERS=2 FANOUT_STRESS_WORKERS=2 \
FANOUT_ITERS=1 FANOUT_STRESS_ITERS=1 RUN_TIMEOUT=10 \
BUILD_DIR=build/cross_lang_perf_docker_toolchain_smoke \
REPORT_PATH=doc/09_report/.docker_cross_language_smoke.md \
PROFILE_DOCKER_MEMORY=2g PROFILE_DOCKER_CPUS=2.0 \
sh scripts/check/check-cross-language-perf.shs
```

Original observed failure:

- `C (gcc)` compiles.
- `Go` compiles.
- `Docker isolation` report metadata records `inside_container=1`.
- Simple native compilation fails for generated profile sources.

Focused native-link error:

```text
error: codegen: linker failed with exit code 1: GNU ld failed
ld: .../libsimple_runtime.a(...): undefined reference to symbol '__tls_get_addr@@GLIBC_2.3'
ld: /lib64/ld-linux-x86-64.so.2: error adding symbols: DSO missing from command line
```

## Impact

Auto-selecting the debug compiler inside Docker regresses the existing profile
script: fresh smoke reports fall back to `compile failed` for Simple native
rows, so the checked profile contract no longer matches the current harness.
Release-wrapper selection still produces full contract-gated cross-language
reports with positive Simple native `thread_spawn` and `multicore_green_spawn`
rows when the release wrapper has been rebuilt. The checked-in release wrapper
is not authoritative until the stale release-binary blocker is closed.

## Release-Path Resolution Evidence

The linker builder now emits `simple_runtime` before libc/pthread/dl/m/gcc_s so
GNU `ld` can resolve symbols introduced by the static Rust runtime archive for
the release-wrapper profile path.

Release-path verification command:

```sh
PROFILE_DOCKER_ISOLATION=1 \
RUNS=1 WARM_IN_PROCESS=1 CPU_WORKERS=4 OS_THREAD_WORKERS=4 \
MULTICORE_GREEN_WORKERS=4 COOPERATIVE_GREEN_WORKERS=4 FANOUT_WORKERS=20 \
FANOUT_MULTICORE_GREEN_WORKERS=20 FANOUT_COOPERATIVE_GREEN_WORKERS=20 \
FANOUT_STRESS_WORKERS=128 FANOUT_ITERS=32 FANOUT_STRESS_ITERS=1 \
RUN_TIMEOUT=20 BUILD_DIR=build/cross_lang_perf_docker_contract_smoke \
REPORT_PATH=doc/09_report/.docker_cross_language_smoke.md \
PROFILE_DOCKER_MEMORY=2g PROFILE_DOCKER_CPUS=2.0 \
sh scripts/check/check-cross-language-perf.shs
```

Result:

```text
profile_report_contract=true
profile_kind=cross_language
```

The generated report included positive `Simple (native)` `thread_spawn`
evidence, positive `Simple multicore green (native)` evidence with
`pool_used=N/N`, `parallelism=N/N`, and `queue_model=work_stealing`, plus C
pthread and Go goroutine rows.

## 2026-06-11 Auto-Selection Correction

The profile wrapper still avoids forwarding a stale host `SIMPLE_BINARY` into
the isolated container when `PROFILE_DOCKER_SIMPLE_BINARY` was not explicitly
set. Docker auto-selection must prefer runnable `bin/simple` /
`bin/release/simple`, but it now probes candidates with `--version` and skips a
stale release wrapper whose wrapped platform binary is missing. It only falls
back to `src/compiler_rust/target/debug/simple` when the release wrapper is
unavailable or stale. Reproduced on 2026-06-11:

```sh
docker run --rm --entrypoint /bin/sh --user "$(id -u):$(id -g)" \
  -v "$PWD:/workspace:rw" -w /workspace --network=none --memory=2g --cpus=2.0 \
  simple-cross-language-perf:latest \
  -lc 'src/compiler_rust/target/debug/simple compile build/cross_lang_perf/hello.spl --native -o /tmp/hello_native_in_docker'
```

Result:

```text
error: codegen: linker failed with exit code 1: GNU ld failed
ld: ... undefined reference to symbol '__tls_get_addr@@GLIBC_2.3'
ld: /lib64/ld-linux-x86-64.so.2: error adding symbols: DSO missing from command line
```

The same container run succeeds with:

```sh
bin/release/simple compile build/cross_lang_perf/hello.spl --native -o /tmp/hello_native_in_docker_release
```

That success requires a release wrapper whose platform binary exists in the
mounted workspace.

Contract-gated Docker evidence:

```sh
PROFILE_DOCKER_ISOLATION=1 PROFILE_DOCKER_IMAGE=simple-cross-language-perf:latest \
PROFILE_DOCKER_MEMORY=2g PROFILE_DOCKER_CPUS=2.0 RUNS=1 CPU_WORKERS=2 \
OS_THREAD_WORKERS=2 MULTICORE_GREEN_WORKERS=8 COOPERATIVE_GREEN_WORKERS=2 \
FANOUT_WORKERS=1000 FANOUT_MULTICORE_GREEN_WORKERS=1000 \
FANOUT_COOPERATIVE_GREEN_WORKERS=20 FANOUT_ITERS=1 \
FANOUT_STRESS_WORKERS=1000 FANOUT_STRESS_ITERS=1 RUN_TIMEOUT=90 \
REPORT_PATH=doc/09_report/cross_language_perf_2026-06-08_docker_contract.md \
sh scripts/check/check-cross-language-perf.shs
```

Result:

```text
profile_report_contract=true
```

The report records positive `thread_spawn` OS-thread evidence and positive
`multicore_green_spawn` M:N candidate evidence. The report header records
`CPU workers: 2`, `Go GOMAXPROCS: 2`, and
`Go scheduler: GOMAXPROCS=2 NumCPU=32`; the profile contract now fails if the
reported Go scheduler width does not match `CPU_WORKERS`. The large fanout
stress rows showed Go `9.260ms`, Simple multicore green native `11.353ms` with
`pool_used=1000/1000`, `parallelism=2/2`, and
`queue_model=work_stealing`, and C pthreads `63.408ms`.

## 2026-06-12 Checked-In Wrapper Smoke

A quick Docker-isolated smoke of the same canonical profile script completed in
a separate container process without crashing, but all Simple native and SMF
rows reported `compile failed` because the checked-in release wrapper target was
missing in this workspace before the auto-selection probe hardened stale-wrapper
detection. C and Go still compiled, proving the Docker image and profile harness
path were usable.

Command shape:

```sh
PROFILE_DOCKER_ISOLATION=1 SKIP_PROFILE_REPORT_CONTRACT=1 \
REPORT_PATH=build/tmp/cross_language_perf_quick_docker_smoke.md \
RUNS=1 WARM_IN_PROCESS=1 CPU_WORKERS=2 OS_THREAD_WORKERS=2 \
COOPERATIVE_GREEN_WORKERS=2 MULTICORE_GREEN_WORKERS=2 \
FANOUT_WORKERS=8 FANOUT_COOPERATIVE_GREEN_WORKERS=8 \
FANOUT_MULTICORE_GREEN_WORKERS=8 FANOUT_ITERS=1 \
FANOUT_STRESS_WORKERS=8 FANOUT_STRESS_ITERS=1 RUN_TIMEOUT=20 \
PROFILE_DOCKER_CPUS=2 PROFILE_DOCKER_MEMORY=2g \
sh scripts/check/check-cross-language-perf.shs
```

Focused failure:

```text
bin/release/simple: line 7: /workspace/bin/release/x86_64-unknown-linux-gnu/simple: No such file or directory
```

Interpretation:

- This is not a new profile script or C/Go toolchain failure.
- It is the checked-in release-wrapper stale-artifact state tracked by
  `multicore_green_release_binary_stale_2026-06-11.md`.
- Auto-selection now treats this broken wrapper as unavailable after a failed
  `--version` probe instead of selecting it just because the shell file is
  executable.
- Contract-gated M:N evidence must continue to cite the checked-in
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
  or a fresh report generated with a rebuilt release wrapper.

## 2026-06-13 Auto-Selection Probe Hardening

The profile harness now probes auto-selected Simple binaries with `--version`
before accepting them. In this workspace, `bin/release/simple` is executable but
its wrapped platform binary is missing, so auto mode correctly skips it and
falls back to the current-source debug compiler instead of measuring a stale
wrapper.

Smoke command shape:

```sh
SKIP_PROFILE_REPORT_CONTRACT=1 RUNS=1 WARM_IN_PROCESS=1 CPU_WORKERS=1 \
OS_THREAD_WORKERS=1 MULTICORE_GREEN_WORKERS=1 COOPERATIVE_GREEN_WORKERS=1 \
FANOUT_WORKERS=2 FANOUT_MULTICORE_GREEN_WORKERS=2 \
FANOUT_COOPERATIVE_GREEN_WORKERS=2 FANOUT_STRESS_WORKERS=2 \
FANOUT_ITERS=1 FANOUT_STRESS_ITERS=1 RUN_TIMEOUT=5 \
BUILD_DIR=build/tmp/cross_lang_autoselect_smoke \
REPORT_PATH=build/tmp/cross_lang_autoselect_smoke.md \
sh scripts/check/check-cross-language-perf.shs
```

Observed report marker:

```text
Simple binary: `src/compiler_rust/target/debug/simple`
```

This does not close the debug-native linker blocker for Docker contract reports;
it only prevents an executable stale wrapper from being selected as if it were a
runnable release path.

---

## Addendum 2026-11-11 (lane ne6, batch p3-ne6)

**Verdict: STALE — premise superseded by the evolved artifact layout.**
This is the oldest row in batch ne6; the docker lane has moved on since June.

Evidence:

1. The companion stale-wrapper record this doc leans on,
   `multicore_green_release_binary_stale_2026-06-11.md`, was CLOSED 2026-09-13
   with a measured finding: `bin/release/` is a per-triple tree
   (`x86_64-pc-windows-msvc`, `aarch64-unknown-linux-gnu`, …), and the
   single checked-in `bin/release/simple` wrapper-plus-delegate arrangement
   this row's auto-selection logic probes "no longer exists as filed".
   `bin/simple` now announces its own provenance (the seed warning is emitted
   by the tracked binary itself — observed in every lane run).
2. The link-order resolution this row credits survives in source:
   `src/compiler_rust/compiler/src/linker/native.rs:342` keeps the
   simple-runtime-archive-before-libc ordering for symbols "introduced by the
   Rust runtime archive, such as `__tls_get_addr`", with tests
   (`pipeline/native_project/tests.rs:7152`,
   `pipeline/native_project/tools.rs:5103`). The pure-Simple linker has its
   own TLS relaxation for the symbol (`src/compiler/70.backend/linker/elf/tls_relax.spl`).
   The surrounding link target has been re-architected to a freestanding
   sysroot (`libsimpleos_c.a`, crt0 — `pipeline/native_project/linker.rs:713-716`),
   far from the June glibc-container state.
3. `scripts/check/check-cross-language-perf.shs` still exists (118 KB) and its
   docker isolation is intact (`PROFILE_DOCKER_ISOLATION` at :42,:171), but
   its binary auto-selection is now a self-hosted identity gate: "the canonical
   `require-self-hosted.shs` identity gate rejects Rust bootstrap seeds;
   unavailable or stale release paths are untestable, never fallback evidence"
   (:1572). The stale-wrapper-fallback class this row tracked is refused by
   construction.
4. Docker is NOT available on the triage host (Windows; `docker` not on PATH),
   so the in-container profile cannot be re-run here and this classification
   rests on 1-3 plus the 5-month-unmoved harness.

Falsifiable re-run grant for a lane with Linux + docker (re-open this row if
it fails): `PROFILE_DOCKER_ISOLATION=1 RUNS=1 CPU_WORKERS=2 OS_THREAD_WORKERS=2
MULTICORE_GREEN_WORKERS=2 COOPERATIVE_GREEN_WORKERS=2 FANOUT_WORKERS=8
FANOUT_MULTICORE_GREEN_WORKERS=8 FANOUT_COOPERATIVE_GREEN_WORKERS=8
FANOUT_ITERS=1 FANOUT_STRESS_WORKERS=8 FANOUT_STRESS_ITERS=1 RUN_TIMEOUT=20
BUILD_DIR=build/cross_lang_perf_ne6_rerun REPORT_PATH=build/review/ne6_docker_smoke.md
PROFILE_DOCKER_MEMORY=2g PROFILE_DOCKER_CPUS=2.0
sh scripts/check/check-cross-language-perf.shs` — expecting
`profile_report_contract=true` or an honest "untestable" marker, never a
stale-wrapper fallback.
