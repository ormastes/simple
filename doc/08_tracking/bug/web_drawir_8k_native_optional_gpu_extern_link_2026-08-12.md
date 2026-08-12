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
