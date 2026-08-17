# Core-C bootstrap bundle misses `rt_is_interpreter_runtime`

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Fix prepared in the Vulkan integration lane. The core-C archive and focused
Rust admission tests pass; the Engine2D staged-font native probe still needs
one fresh build/run after the session verification cap resets.

## Reproduction

Using the manifest-attested pure-Simple Stage3 compiler with SHA-256
`feb067441c16dc799e7ac92de2a9b6d484cdad6d5e4015c95ee43005b03057c7`,
build `probes/dg_engine2d_text_pixels.spl` with:

- `--runtime-bundle core-c-bootstrap`
- `--source src/lib --source probes`
- `--entry-closure`
- the trusted Winit, runtime, and runtime-C provider dylibs in
  `SIMPLE_LINK_OBJECTS`

The 185-module source closure compiles, but the final arm64 link fails:

```text
Undefined symbols for architecture arm64:
  "_rt_is_interpreter_runtime"
```

References come from CUDA module loading and
`gpu_sffi_uses_interpreter_array_abi`. The declaration is public in
`src/runtime/simple_core/core_process.spl`, and implementations exist in
`src/runtime/runtime.c` and the Rust bootstrap runtime, but the admitted
core-C bundle/provider set does not export the symbol.

Linking without the core-C bundle produces a binary, but it cannot start
because core runtime symbols such as `_rt_cstring_to_text` remain unresolved.
Injecting the existing runtime providers supplies `_rt_cstring_to_text`, but
still does not supply `_rt_is_interpreter_runtime`.

## Required fix

Make `rt_is_interpreter_runtime` part of the supported
`core-c-bootstrap` ABI, or remove the unconditional native closure dependency
from GPU SFFI dispatch. Do not restore removed hosted/Rust fallback bundles.

The prepared fix exports a native-false implementation from the existing
`runtime_native.c` standalone owner, promotes the symbol into
`CORE_REQUIRED_RUNTIME_SYMBOLS`, and adds archive and behavior assertions.

## Acceptance

1. The focused probe links with `core-c-bootstrap` and trusted providers.
2. `nm -u` shows no unresolved `rt_is_interpreter_runtime`.
3. The native probe starts and reaches its staged-quads assertions.
4. The trusted macOS Vulkan 2D harness builds with the same runtime lane.
