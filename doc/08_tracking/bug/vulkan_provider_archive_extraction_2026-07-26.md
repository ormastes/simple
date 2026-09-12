# Vulkan Provider Archive Extraction

## Status

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

Source fixed. The focused linker regression passes 13/13, and the canonical
external-provider owner repair has a host-independent archive fixture. A fresh
source-matched Linux/Vulkan execution is still required before TODO 580 or any
WM acceptance criterion can close.

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

## Owner Repair

`SIMPLE_LINK_OBJECTS` remains the explicit provider admission boundary. The
LLVM native-link owner scans only caller-selected static providers with
`llvm-nm`/`nm`. When one strongly defines
`rt_vulkan_provider_is_available`, it forwards that exact symbol through
`NativeLinkConfig`. The platform linker renders both the exact extraction root
and dynamic-export visibility before the archive (`--undefined` plus
`--export-dynamic-symbol`, Darwin `-u` plus `-export_dynamic`, or MSVC
`/INCLUDE` plus `/EXPORT`) so the strong provider member is extracted and the
core runtime can discover it with `dlsym(RTLD_DEFAULT, ...)`.

The repair deliberately does not use `--whole-archive`: unrelated optional GPU
members remain quarantined and unreferenced providers are not selected.

`scripts/check/check-vulkan-provider-archive-retention.shs` builds a two-member
archive in weak-first order. The weak member mirrors the production
`dlsym(RTLD_DEFAULT, ...)` lookup and has no unresolved provider reference. Its
baseline reaches availability `0`; the canonical root-plus-export policy
reaches the strong provider value `73`. This is link/archive/runtime-symbol
evidence only. It does not execute Vulkan, enumerate a device, render, present,
or read back pixels. MSVC receives exact extraction/export flags. MinGW
receives retention only and no ELF export flag because its provider lookup
implementation remains a separate runtime concern.

The remaining readback failure is tracked separately in
`native_engine2d_readback_cross_module_field_layout_2026-07-26.md`.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
