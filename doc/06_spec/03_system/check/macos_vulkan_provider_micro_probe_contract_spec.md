# macOS Vulkan Provider Micro-Probe Contract

The contract keeps the diagnostic below rendering and window creation.

## Direct provider probe

The pure-Simple probe must:

1. Open the exact provider path supplied as its only argument.
2. Resolve the provider availability and device-count aliases.
3. Check availability before initialization; initialize before querying device
   count; and shut down only after successful initialization.
4. Resolve `rt_vulkan_get_last_error` but do not invoke it through
   `DynLib.call0`: its text return ABI has no typed dynamic-call bridge. Emit
   `vulkan_provider_probe_provider_error_abi=blocked` instead.
5. Emit fail-closed structured fields when loading or symbol resolution fails.

It must not reference Engine2D, VulkanBackend, or winit.

## Self-hosted checker

The checker must:

1. Require a trusted build manifest that binds the canonical repository release
   compiler path and SHA-256, and reject `compiler_rust/target` overrides.
2. Build with `SIMPLE_NO_STUB_FALLBACK=1`.
3. Record the provider path and SHA-256 plus bounded, hashed native-build and
   probe-output evidence.
4. Use `DYLD_PRINT_LIBRARIES=1` to verify the provider image loaded.
5. Avoid the full-live Vulkan checker.

## Current result

The focused source contract passed 2/2 on 2026-07-26. The subsequent native
build stopped in the self-hosted compiler before probe execution; see
`doc/09_report/macos_vulkan_provider_micro_probe_2026-07-26.md`.
