# Vulkan DrawIR showcase native build exceeds 10 minutes

## Status

Open. This blocks live Simple-to-Rust validation of the no-readback Vulkan
DrawIR presentation entry, but does not invalidate the passing Rust runtime
and source-contract evidence.

## Reproduction

```sh
bin/simple native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure \
  --entry src/app/ui_showcase/hosts/main_2d_vulkan.spl \
  --strip \
  --output build/vulkan_drawir_no_readback/simple_showcase_vulkan
```

On 2026-08-11 the entry worker remained CPU-active at 100% for more than ten
minutes, used approximately 2.1% host memory, emitted no progress after
front-end warnings, and created no output artifact. The attempt was terminated
once; it was not retried.

## Expected

The focused entry closure should either produce the executable within a bounded
developer iteration budget or fail with a stage/progress diagnostic identifying
the slow compilation unit.

## Required follow-up

1. Emit per-stage and current-module timing from `native_build_worker.spl`.
2. Identify whether closure discovery, lowering, optimization, code generation,
   or linking owns the CPU time.
3. Add a warm-cache build-time receipt and a fail-fast budget for this entry.
4. After correction, run the live Xvfb/lavapipe showcase and require distinct
   verified-readback, submit-only, and retained-present receipts.

## Bounded repro and deployment admission (2026-08-12)

Two bounded probes were run instead of repeating the original unbounded build.
Adding `--timeout 45 --verbose` took the native-build parent roughly 42
seconds to spawn its interpreted worker. The worker then consumed its budget
before `cli_native_build` ran: no closure-timing, compiler-phase, or
`SIMPLE_BUILD_PROGRESS_EVENTS` receipt was created.

The original argument shape, enclosed in an external 45-second watchdog, also
spawned the worker. Killing only that outer parent left the worker's own
`timeout ... simple run native_build_worker.spl` process alive. It was
explicitly terminated; no output was produced. An external one-PID watchdog
is therefore not safe containment for this launcher.

The active `bin/simple --version` prints the repository's `Rust-built Simple
binary is a bootstrap seed only` rejection banner. The capability selector
(`SIMPLE_COMPILER_PROBE_TIMEOUT=5 sh scripts/lib/simple-compiler-select.shs
--root . --quiet`) found no eligible self-hosted compiler in the staged/release
search set. A native showcase result from this workspace is inadmissible even
if it eventually links.

`scripts/check/build-vulkan-drawir-showcase-native.shs` is the replacement
deployment gate. It first requires `simple_compiler_usable`, then delegates a
bounded worker lifetime (`--timeout`, default 180 seconds) and writes closure,
phase, and progress receipts beside the requested artifact. It exits `6`
before build on the current seed-only state rather than consuming the old
ten-minute budget. This is a fail-closed deployment fix, not an 8K/80 result.
