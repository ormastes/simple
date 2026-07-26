# Vulkan Engine2D Readback Evidence

- status: blocked
- reason: Vulkan provider archive member not extracted
- host: Linux x86_64
- ICD: `/usr/share/vulkan/icd.d/nvidia_icd.json`
- execution mode: native, no stub fallback

## Source-Matched Compiler

`build/gpu-goal/source-matched/simple` was built incrementally from the fixed
compiler source:

```text
Build complete: 3 compiled, 682 cached, 0 failed
Time: 20.0s compile + 59.7s link
```

No Stage2, Stage4, Cargo build, bootstrap script, cache deletion, or seed
fallback ran.

## Evidence Build

The source-matched compiler emitted the 184-module Engine2D evidence closure.
The guarded core link correctly rejected unrelated optional GPU symbols. A
direct no-stub link of the retained objects then succeeded with the existing
optional-GPU provider archive and current quarantine-lock provider.

## Execution

The binary starts without the prior aggregate-field crash, but stops before
readback:

```text
vulkan_probe_available=false
vulkan_probe_diagnostic=requested=vulkan;selected=vulkan;status=Unavailable;api=vulkan;gate=vulkan_runtime;shader=spirv;compute=false;graphics=false;present=false;reason=Vulkan shared session initialization failed: availability
overall=fail
```

The archive contains a weak compatibility `rt_vulkan_is_available` and a
strong provider-only `rt_vulkan_provider_is_available`. The weak member is
extracted first, leaving no unresolved reference that pulls the provider-only
member. Hardware readback, handle/identity, checksum, and parity pass are not
claimed.

See
`doc/08_tracking/bug/vulkan_provider_archive_extraction_2026-07-26.md`.
