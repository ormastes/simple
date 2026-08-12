# Web DrawIR 8K native optional-GPU extern link failure — 2026-08-12

## Status

Open. The native-typed retained Web/DrawIR benchmark compiles with the admitted
pure-Simple compiler and Cranelift, but cannot link against `simple-core`.

## Reproduction

```sh
SIMPLE_BIN=build/evidence-stage3-fix/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple \
WEB_DRAWIR_8K_BUILD_DIR=/dev/shm/web-drawir-8k-native-simple-core \
scripts/check/build-web-drawir-8k-native.shs
```

The entry closure compiles, then the linker reports unresolved runtime symbols
from optional Engine2D families including CUDA, Vulkan, Metal, ROCm, pointer
helpers, environment access, and `rt_file_hash_sha256`. The selected benchmark
backend is software, but importing the canonical `Engine2D` backend owner keeps
these sibling externs in the native link closure.

`rust-hosted` is not a valid workaround: the admitted compiler explicitly
reports that bundle was removed and recommends `simple-core` or
`core-c-bootstrap`. `simple-core` was tested and still leaves the externs
unresolved.

## Acceptance

- Native entry-closure/linking must exclude unreachable optional backend externs
  or link the authoritative hosted runtime implementations without fabricated
  stubs.
- `SIMPLE_NO_STUB_FALLBACK=1` must remain enabled.
- The cached artifact must execute the canonical typed revision-cache API and
  emit the complete 7680x4320 p50/p95/RSS/fallback/readback/checksum receipt.
- This failure occurs before execution and is not an 8K performance result.

## Runtime-authority follow-up

Passing the admitted compiler's sibling
`stage2-runtime-authority` through `--runtime-path` substantially reduces the
unresolved set, but `core-c-bootstrap` still lacks current strided Vulkan,
Engine2D SIMD blend, Intel, WebGPU, OneAPI, OpenGL, TLS SHA-256, environment, and
sleep symbols. Both supported bundles were tested; `core-c-bootstrap` is the
compiler-recommended default for this hosted transitional lane.

An attempted current runtime archive build used:

```sh
CARGO_TARGET_DIR=/dev/shm/simple-vk-runtime-target \
  cargo build -p simple-runtime --features vulkan
```

It failed before archive emission because concurrent runtime work currently has
three missing `rt_pg_parallel_worker_handoff_*` exports in `runtime/src/lib.rs`
and passes the `extern "C"` function `rt_shared_get` directly to `Option.map` in
`runtime/src/value/objects.rs`. These are runtime build blockers, not rendering
measurements, and were not changed by this lane.
