# Unit TLDR summary surface has zero content identity -> "conflicting physical source"

- **Status:** verification-pending
- **Date:** 2026-11-16
- **Area:** compiler / 80.driver (unit TLDR imports), 20.hir module surface registry
- **Introduced by:** #9542 (`269ec58d0c1`, bind unit TLDR import surfaces across lib./std. alias rows)

## Symptom

Every cross build of lint / test-runner with the phase-2 compiler built from
`ef09036bfa8f` failed:

```
Module surface extraction error: conflicting physical source:
  .../build/scv/snapshots/scv-revision-v2-.../src/lib/common/string_core.spl
  module='std.common.string_core' index=177
```

## Root cause

A `src/lib` file is admitted under two rows (`lib.X` and its `std.X` twin) with
one canonical path. Since #9542 the first row gets the TLDR summary surface
(`unit_tldr_surface_for_row_v1`). The second row then takes the registry alias
lane (`ModuleSurfaceBuilder.add_alias_canonical_identity`), which requires the
registered surface's `content_length`/`content_hash` to match the row source.
`module_surface_from_tldr_v1` builds surfaces with both fields 0, and
`unit_tldr_plan_v1` only rebound `canonical_path`, so the check always failed.
Not a stale-snapshot / cache-key issue: the mismatch is deterministic.

## Fix

`unit_tldr_plan_v1` binds `content_length` and `content_hash` (same
`rt_hash_text` the alias lane compares, via `module_surface_content_hash`) from
the source it already read.

## Tests

`test/01_unit/compiler/80.driver/unit_tldr_surface_content_identity_spec.spl`.
