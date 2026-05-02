# Remote Baremetal Capability Negative Matrix

**Date:** 2026-04-21
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 190
**Status:** Closed

## Research

- `test/system/remote_baremetal_lane_status_spec.spl` already owns lane registry and capability probe behavior.
- `stm32h7_openocd` and `stm32h7_trace32` are host-aware authoritative lanes, so missing local tools must skip acceptably rather than fail the lane matrix.
- The existing `probe_openocd()` and `probe_trace32()` functions depended on the developer machine PATH, which made negative coverage non-deterministic.

## Plan

- Add deterministic probe helpers that build OpenOCD and TRACE32 reports from explicit tool availability.
- Keep shell-backed probes as wrappers around those helpers.
- Add focused system coverage for missing OpenOCD and TRACE32 tools on host-aware lanes.
- Close row 190 after lint and the focused system spec pass.

## Fix

- Added `probe_openocd_capability(false)` and `probe_trace32_capability(false)` coverage.
- Verified missing tools produce `skip_missing_tool`, are not runnable, and remain acceptable.
- Closed `todo_db.sdn` row 190.

## Verification

```sh
bin/simple lint src/lib/nogc_sync_mut/debug/remote/exec/capability_report.spl
bin/simple lint test/system/remote_baremetal_lane_status_spec.spl
bin/simple test test/system/remote_baremetal_lane_status_spec.spl
```
