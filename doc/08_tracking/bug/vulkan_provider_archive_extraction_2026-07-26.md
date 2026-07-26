# Vulkan Provider Archive Extraction

## Status

Source fixed. The focused linker regression passes 13/13. Deployment is folded
into TODO 580's next source-matched incremental compiler build.

## Evidence

Forcing the provider-only member during the retained no-stub link changed the
hardware result to:

```text
vulkan_probe_available=true
status=Initialized
compute=true
graphics=true
strict_create_status=pass
backend_name=vulkan
```

The provider archive contains both a weak core-C `rt_vulkan_is_available` and
the strong Rust `rt_vulkan_provider_is_available`. Normal archive extraction
can pull the weak member first; after that no unresolved public symbol remains
to extract the provider member. The core-C function then resolves the
provider-only name with `dlsym`, finds nothing, and returns unavailable.

## Fix

`native_all_gnu_support_args` now retains
`rt_vulkan_provider_is_available` on ELF/MinGW and
`_rt_vulkan_provider_is_available` on macOS whenever native-all is selected.
The remaining readback failure is tracked separately in
`native_engine2d_readback_cross_module_field_layout_2026-07-26.md`.
