# Bug: Fresh module export loses owner metadata

- **Date:** 2026-07-25
- **Status:** open
- **Severity:** high
- **Area:** Rust bootstrap interpreter module loading
- **TODO:** 582

## Problem

`cache_module_exports` records an owner against the `Arc<Dict>` in
`exports_value`. The fresh-load return path later constructs another
`Arc<Dict>` from the same map. `module_exports_owner` keys by dictionary pointer,
so the returned value has no owner and runtime `record_import_binding` cannot
record exact provenance.

## Repair

Reuse the cached `exports_value` for the fresh full-module return. Preserve the
specific-item return path.

## Acceptance

Add an unflattened three-module regression where a facade imports an aliased
growing global, calls its defining module to mutate it, and then reads the alias.
Require the existing 14-test flattened/global-owner suite plus the new
unflattened case to pass once.
