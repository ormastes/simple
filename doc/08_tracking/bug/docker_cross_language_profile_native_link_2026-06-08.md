# Docker Cross-Language Profile Native Link Blocker

## Status

Open.

## Summary

`PROFILE_DOCKER_ISOLATION=1` with `simple-cross-language-perf:latest` now runs
the existing cross-language profile script in a separate Docker process with C
and Go toolchains available. C pthread and Go goroutine rows compile and run,
but Simple native rows fail during native linking inside the container.

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

Observed:

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

The Docker image is valid for crash-isolated C/Go toolchain smoke evidence, but
it is not yet sufficient for a full contract-gated cross-language profile
because the checked profile contract requires positive Simple native
`thread_spawn` and `multicore_green_spawn` rows.

## Next Step

Fix the Simple native linker invocation for the container toolchain so the
runtime archive links the needed TLS/libc symbols, then rerun the same Docker
profile command without `SKIP_PROFILE_REPORT_CONTRACT`.
