# FPGA JTAG ZedBoard Public Exclusion

**Date:** 2026-04-21
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 192
**Status:** Closed

## Research

- `fpga_jtag_zedboard` has no authoritative spec in `doc/08_tracking/lane_matrix.md`.
- `src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl` is the source of truth for generated/status views.
- Existing reports describe the lane as quarantined because the real JTAG chain plus upload/run/result proof has not been established.
- The lane matrix already recommended public exclusion, but the status table and summary still listed the lane as `in_progress`, leaving the TODO unresolved.

## Plan

- Keep the hardware work visible as a future/postponed milestone.
- Mark the lane as excluded from the public supported lane set.
- Preserve the reason: structural-only proof, no authoritative compiled execution result.
- Close the tracking row as a decision item, not a hardware completion item.

## Fix

- Added first-class `LaneStatus.excluded_public`.
- Updated `src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl` to classify `fpga_jtag_zedboard` as `excluded_public`.
- Updated `src/lib/nogc_sync_mut/debug/remote/exec/lane_status.spl` and `test/system/remote_baremetal_lane_status_spec.spl` for public-exclusion reporting.
- Updated `doc/08_tracking/lane_matrix.md` to classify `fpga_jtag_zedboard` as `excluded_public` and align the table with the registry's existing `riscv_external_formal` lane.
- Closed `todo_db.sdn` row 192 with the decision issue id.

## Verification

```sh
rg -n "fpga_jtag_zedboard|excluded_public|Publicly excluded" doc/08_tracking/lane_matrix.md
rg -n "192, TODO" doc/08_tracking/todo/todo_db.sdn
bin/simple lint src/lib/nogc_sync_mut/debug/remote/exec/lane_descriptor.spl
bin/simple lint src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl
bin/simple lint src/lib/nogc_sync_mut/debug/remote/exec/lane_status.spl
bin/simple lint test/system/remote_baremetal_lane_status_spec.spl
bin/simple test test/system/remote_baremetal_lane_status_spec.spl --force-rebuild
```
