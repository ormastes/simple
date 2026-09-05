# Theme Sync Dump Local Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #THEME-SYNC-001 |
| Category | Tooling / Theme Sync |
| Status | Implemented |
| Type | Unit Spec |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/ui/theme_sync/theme_sync_dump_local_test.spl` |
| Coverage Target | `src/lib/common/ui/theme_sync_sdn.spl` |
| Generator | Manual mirrored SSPEC doc |

## Overview

Verifies SDN serialization for local Stitch design systems and round-trip
parsing back into parsed design-system values.

## Scenarios

Generated from executable SPipe scenarios in the source test. The source covers
root metadata fields, theme fields, named colors, omitted non-SDN fields,
unknown-field tolerance, and serializer/parser round trips.
