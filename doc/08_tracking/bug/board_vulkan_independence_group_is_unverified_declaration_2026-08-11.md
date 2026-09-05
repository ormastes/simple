# `independence_group` is an unverified declaration — a mislabel is undetectable today

**Date:** 2026-08-11
**Category:** OS / GPU driver / counterpart evidence
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Owner:** Board Vulkan lane L4 (host provider inventory)
**Files:** `src/os/drivers/gpu/board_vulkan/provider_inventory.spl`,
`test/01_unit/os/vulkan/provider_inventory_spec.spl`

## Summary

`ProviderManifest.independence_group` (frozen in
`src/lib/common/spec/evidence/counterpart/model.spl`) is the field that stops
several ICDs built from one upstream engine from being counted as several
independent references — `provider_inventory_independent_reference_count`
counts distinct `independence_group` values. Today that field is a **plain
string the manifest author writes by hand**. Nothing checks it against the
host. If a manifest author relabels lavapipe's `independence_group` away from
`mesa` — by mistake or by malice — the count of independent references
silently inflates, and nothing in `provider_inventory.spl`,
`provider_manifest_rejections`, or the independence predicate itself notices.

This was found while writing the sabotage proof for lane L4's provider
inventory: an initial version of the spec asserted that this relabel "gets
caught" because the count changes from 1 to 2 — but a count *changing* is not
a count being *validated*. The changed count is the bug the field exists to
prevent, not evidence that it was prevented. The spec has been corrected to
assert the miscount honestly (a demonstrated gap) rather than claim it is
caught.

## Reproduction

```
# All these resolve to ONE upstream package on this host:
$ dpkg -S /usr/lib/x86_64-linux-gnu/libvulkan_intel.so
mesa-vulkan-drivers:amd64: /usr/lib/x86_64-linux-gnu/libvulkan_intel.so
$ dpkg -S /usr/lib/x86_64-linux-gnu/libvulkan_lvp.so
mesa-vulkan-drivers:amd64: /usr/lib/x86_64-linux-gnu/libvulkan_lvp.so
$ dpkg -S /usr/lib/x86_64-linux-gnu/libvulkan_radeon.so /usr/lib/x86_64-linux-gnu/libvulkan_nouveau.so \
          /usr/lib/x86_64-linux-gnu/libvulkan_asahi.so /usr/lib/x86_64-linux-gnu/libvulkan_virtio.so
# -> all four also: mesa-vulkan-drivers:amd64
```

But in `provider_inventory.spl`, `independence_group` is just a `pub val` text
constant assigned by hand at each `ProviderManifest` construction site. Change
`provider_lavapipe()`'s `independence_group` to any other string and:

- `provider_manifest_rejections` does not fire (it only checks the field is
  non-empty, not that it is *correct*).
- `provider_inventory_independent_reference_count([anv, radv, lavapipe])`
  returns 2 instead of the honest 1, and nothing flags the discrepancy.

## Why this matters

This is exactly the failure class `independence_group` was invented to
prevent (model.spl's own comment: "what stops two wrappers over one upstream
engine from being counted as two independent references"). A field that
prevents a failure only when honestly filled in, with no check against the
thing it claims to describe, is a documentation comment with extra steps.

## Concrete unblock condition (suggested by red-team audit, agreed)

Derive the independence group from the host instead of trusting the
declaration, and assert `declared_group == derived_group`:

1. For a native ICD, resolve the pinned `.so` path's owning package via
   `dpkg -S <path>` (Debian/Ubuntu) or the equivalent for other distros.
2. Map package name -> canonical independence group (e.g.
   `mesa-vulkan-drivers` -> `mesa`, `glslang-tools` -> `khronos-glslang`).
3. A manifest whose declared `independence_group` disagrees with the derived
   one is rejected the same way an empty `artifact_hash` is rejected today.

This needs a real process-exec (or equivalent host-package-query) capability
reachable from pure Simple with a stable, testable contract — not shelling out
ad hoc from inside a spec. That capability was not available/verified within
this lane's time budget; scoping it is the actual unblock work item here.

## What's fixed today, and what isn't

- **Fixed / genuine today:** empty `artifact_hash` is rejected
  (`provider_manifest_rejections`); wrong `abi_version` is rejected (same
  function). Both are exercised as red-then-restored sabotage proofs in
  `test/01_unit/os/vulkan/provider_inventory_spec.spl`.
- **Not fixed, tracked here:** `independence_group` correctness. The spec's
  "sabotage 3" test documents the gap by asserting the actual (wrong) behavior
  — the relabel inflates the count and nothing catches it — rather than
  falsely claiming detection.

## Status

Open. Not blocking lane L4's inventory delivery (the inventory's own
`independence_group` values were independently verified via `dpkg -S` at
authoring time, see the plan doc's "Provider inventory" section), but blocking
any FUTURE manifest whose author does not do that verification by hand.
