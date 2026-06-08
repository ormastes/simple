# Docker Cross-Language Profile Native Link Blocker

## Status

Fixed by `src/compiler_rust/compiler/src/linker/native.rs` ordering Simple
static runtime libraries before dependent system libraries for GNU-style
linkers.

## Summary

`PROFILE_DOCKER_ISOLATION=1` with `simple-cross-language-perf:latest` runs the
existing cross-language profile script in a separate Docker process with C and
Go toolchains available. Before the fix, C pthread and Go goroutine rows
compiled and ran, but Simple native rows failed during native linking inside
the container.

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

Before the fix, the Docker image was valid for crash-isolated C/Go toolchain
smoke evidence but could not produce a full contract-gated cross-language
profile because the checked profile contract requires positive Simple native
`thread_spawn` and `multicore_green_spawn` rows.

## Resolution Evidence

The linker builder now emits `simple_runtime` before libc/pthread/dl/m/gcc_s so
GNU `ld` can resolve symbols introduced by the static Rust runtime archive.

Verification command:

```sh
PROFILE_DOCKER_ISOLATION=1 SIMPLE_BINARY=src/compiler_rust/target/debug/simple \
PROFILE_DOCKER_SIMPLE_BINARY=src/compiler_rust/target/debug/simple \
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

## 2026-06-08 Docker Auto-Selection Refresh

The profile wrapper now avoids forwarding a stale host `SIMPLE_BINARY` into the
isolated container when `PROFILE_DOCKER_SIMPLE_BINARY` was not explicitly set.
Inside Docker it auto-selects `src/compiler_rust/target/debug/simple` when that
fixed compiler is present, then falls back to the usual release wrappers. It
also exports `GOMAXPROCS=CPU_WORKERS` unless the caller explicitly overrides
`GOMAXPROCS`, so Go goroutine rows and Simple multicore-green rows use the same
scheduler-width limit.

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

The report records `Simple binary: src/compiler_rust/target/debug/simple`,
positive `thread_spawn` OS-thread evidence, and positive
`multicore_green_spawn` M:N candidate evidence. The report header records
`CPU workers: 2`, `Go GOMAXPROCS: 2`, and
`Go scheduler: GOMAXPROCS=2 NumCPU=32`; the profile contract now fails if the
reported Go scheduler width does not match `CPU_WORKERS`. The large fanout
stress rows showed Go `9.260ms`, Simple multicore green native `11.353ms` with
`pool_used=1000/1000`, `parallelism=2/2`, and
`queue_model=work_stealing`, and C pthreads `63.408ms`.
