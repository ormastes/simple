# Remote Baremetal Result Channels

**Date:** 2026-04-21
**Todo:** `doc/08_tracking/todo/todo_db.sdn` row 189
**Status:** Closed

## Research

- `test/system/remote_baremetal_lane_status_spec.spl` already verifies `ResultPacket` constructors and registry lane counts.
- `LaneRegistry.default()` is the source of truth for stable and host-aware lanes.
- The missing coverage was not packet construction; it was asserting the authoritative lane result-channel contract across the registry.

## Plan

- Add registry-level assertions for every authoritative lane.
- Require every authoritative lane to have an authoritative spec path.
- Assert representative named lane contracts for semihost, exit-code, register-readback, debugger-console, and RAM-sentinel result channels.
- Close row 189 after lint and the focused system spec pass.

## Fix

- Added result-channel contract tests to `test/system/remote_baremetal_lane_status_spec.spl`.
- Verified representative authoritative lane contracts for semihost, exit-code, register-readback, debugger-console, and RAM-sentinel result channels.
- Closed `todo_db.sdn` row 189.

## Verification

```sh
bin/simple lint test/system/remote_baremetal_lane_status_spec.spl
bin/simple test test/system/remote_baremetal_lane_status_spec.spl
```
