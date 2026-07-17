# SimpleOS Font Legal Bundle Specification

> Pure-Simple contract for the runtime/legal projection consumed by every
> SimpleOS image builder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

## Scenario: Project the closed bundle

1. Load the shared immutable font pins.
2. Project exactly 53 entries beneath `/SYS/FONTS`: 50 Google Fonts files,
   the CLDR license, root `LICENSE`, and `THIRD_PARTY_NOTICES.md`.
3. Require unique guest long paths and unique collision-free 8.3 aliases.
4. Resolve pinned resources and root notices beneath installed, portable, and
   Windows package roots while leaving unmanaged paths unchanged.

## Scenario: Preserve the runtime boundary

The 16 TTFs retain their existing registry-owned long paths and short aliases.
Only the CLDR license enters the guest; the three XML inputs plus `TAG.txt`,
`SOURCE.sdn`, and `RANKING.sdn` remain build-time ranking evidence.

## Scenario: Fail closed

Pinned companion bytes must match `selected_font_bundle_asset_pins()`. Missing,
empty, stale, or unmanaged companion inputs are rejected before staging. Root
license/notices are transport-owned and must be present and nonempty.

## Executable source

`test/01_unit/os/port/simpleos_font_bundle_spec.spl`
