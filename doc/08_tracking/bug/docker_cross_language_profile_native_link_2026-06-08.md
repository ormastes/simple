# Docker Cross-Language Profile Native Link Blocker

## Status

Partially fixed. Release-wrapper profile runs now pass in Docker, but the debug
compiler path `src/compiler_rust/target/debug/simple` still reproduces the
native linker failure inside the container.

## Summary

`PROFILE_DOCKER_ISOLATION=1` with `simple-cross-language-perf:latest` runs the
existing cross-language profile script in a separate Docker process with C and
Go toolchains available. The release-wrapper compiler path now supports
contract-gated Simple native rows inside the container, but the debug compiler
path still fails during native linking.

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
rows.

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
set. However, Docker auto-selection must prefer `bin/simple` /
`bin/release/simple` and only fall back to `src/compiler_rust/target/debug/simple`
when the release wrapper is unavailable. Reproduced on 2026-06-11:

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
