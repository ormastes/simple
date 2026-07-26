# Vulkan Provider Archive Extraction

## Status

Open. Blocks source-matched Engine2D readback evidence under TODO 580.

## Evidence

The source-matched no-stub evidence binary links successfully, but both it and
the prior reference binary report:

```text
vulkan_probe_available=false
reason=Vulkan shared session initialization failed: availability
```

The provider archive contains both a weak core-C `rt_vulkan_is_available` and
the strong Rust `rt_vulkan_provider_is_available`. Normal archive extraction
can pull the weak member first; after that no unresolved public symbol remains
to extract the provider member. The core-C function then resolves the
provider-only name with `dlsym`, finds nothing, and returns unavailable.

## Required Fix

The native linker must retain `rt_vulkan_provider_is_available` whenever it
selects a Vulkan provider archive. Add a focused archive-order regression:
weak compatibility owner first, strong provider in a later member, and a
runtime assertion that availability reaches the provider.
