# Simplebox applet inventory, count constants and catalog specs disagree (2026-10-30)

Status: open
Area: os/tools/simplebox, os/kernel/loader (primary tool catalog bundle)
Found by: Lunar loader sweep, cluster "array index out of bounds: index is 0 but length is 0"

## Symptom

- `test/01_unit/os/kernel/loader/primary_linux_tool_catalog_bundle_v1_spec.spl`: 3 of 6 fail
  with `array index out of bounds: index is 0 but length is 0`.
- `test/01_unit/os/kernel/loader/simplebox_primary_tool_catalog_bundle_v1_spec.spl`: 4 of 5 fail
  (same index error, plus `CanonicalIdentityMismatch` vs `SignedRecordShapeInvalid`, plus
  `indexed field assignment target is not a writable place`).

## Root cause

This is not a loader or interpreter defect. The tree has two incompatible versions of the
Simplebox command surface. The 2026-08-27 tournament merge (`e274cd33719`) and the
2026-09-29 transplant (`88aac2ffe28`) mixed them:

| Source | Applets |
|---|---|
| `src/os/tools/simplebox/simplebox_inventory_v1.spl` (`_SIMPLEBOX_INVENTORY_APPLET_NAMES_V1`) | 8 (`echo true false pwd seq cat head wc`) |
| `src/os/tools/simplebox/simplebox_artifact_contract.spl` `SIMPLEBOX_APPLET_COUNT_V1` / `..._ALIAS_COUNT_V1` | 41 / 42 |
| `src/os/kernel/loader/primary_linux_tool_catalog_bundle_v1.spl` `PRIMARY_LINUX_TOOL_COMMAND_COUNT_V1` | 12 (= 8 + 4) |
| `src/os/tools/simplebox/simplebox_main.spl` routing | 41 applets, all implementations present |
| `test/01_unit/os/tools/simplebox_dispatch_spec.spl` | "returns all 41 applets" |
| `test/01_unit/os/kernel/loader/simplebox_primary_tool_catalog_bundle_v1_spec.spl` | literal 42 aliases |
| `test/01_unit/os/kernel/loader/primary_linux_tool_catalog_bundle_v1_spec.spl` | literal twelve-command list |

`primary_linux_tool_launch_matrix_v1` returns `[]` when
`simplebox_applet_names_v1().len() != SIMPLEBOX_APPLET_COUNT_V1` (8 != 41). The callers then
index `rows[0]` and fail. The Simplebox bundle plan uses the same count and fails the same way.

## Why it is not fixed here

The 8-entry inventory has a comment calling it "deliberately the routed Simplebox surface,
not a wishlist", and a newer, more detailed twelve-command spec matches it. The dispatcher,
the dispatch spec and the count constants all say 41. Choosing one would rewrite one of two
contradictory specs, and that is a product decision for the SimpleOS owner. Restoring 41
means bringing back the 41-entry inventory from `f685ba8da03`, the per-command capability
table and `COMMAND_COUNT = 45` from `08b93ac8fe9`, and the forty-five-row primary spec.

## Pending markers

The failing examples in both catalog specs are marked `pending(...)` and point to this file.

## Separate, still-open item

`simplebox_primary_tool_catalog_bundle_v1_spec.spl` "rejects every post-plan identity mutation"
also hits `invalid assignment: indexed field assignment target is not a writable place` on
`changed_path.records[0].canonical_path = ...` (nested indexed struct field write) under the
Rust seed interpreter. That is a seed limitation, independent of the count drift.
