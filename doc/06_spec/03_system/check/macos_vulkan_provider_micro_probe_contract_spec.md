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

1. Select the exact compiler and provider recorded by the canonical trusted
   build manifest; caller compiler, provider, and manifest overrides are
   forbidden.
2. Accept only the producer-issued identity/source-kind pair for the current
   frozen Stage-3 compiler. The Stage-3 manifest is reverified by the canonical
   trusted-build producer.
3. Require an executable, non-symlinked compiler with its exact manifest SHA-256,
   reject Rust seed/bootstrap-seed/debug identities, and require the canonical
   default provider paths and hashes.
4. Build with `SIMPLE_NO_STUB_FALLBACK=1`.
5. Record the provider path and SHA-256, an exactly shell-quoted native-build
   command (environment, compiler, and every argument), plus bounded, hashed
   native-build and probe-output evidence. The native-build stream is drained
   through a deterministic bounded transcript: complete output through 8 KiB,
   then a 4 KiB head + 4 KiB tail with an omission marker. The retained log has
   an 8,256-byte hard cap; no unbounded raw build log is retained.
   The cap is checked on both successful and failed native-build attempts.
6. Use `DYLD_PRINT_LIBRARIES=1` to verify the provider image loaded.
7. Avoid the full-live Vulkan checker.

## Current result

The focused source contract passed 2/2 on 2026-07-26. The subsequent native
build stopped in the self-hosted compiler before probe execution; see
`doc/09_report/macos_vulkan_provider_micro_probe_2026-07-26.md`.
The three-cycle native limit remains closed; the manifest-admission repair was
reviewed statically and did not launch another compiler or probe.
