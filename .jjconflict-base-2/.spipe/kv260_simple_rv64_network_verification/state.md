# KV260 Simple RV64 Network Verification

## Status

In progress.

## Acceptance Criteria

- Physical evidence validation is separate from QEMU/RTL evidence.
- The validation lane requires the current KV260 bitstream startup marker.
- The validation lane requires PL UART boot markers from the Simple RV64 softcore.
- The validation lane requires an explicit physical network transport mapping.
- The validation lane requires SimpleOS network readiness, HTTP `/health` and `/` 200 responses, and SSH banner/login evidence.
- The validation lane exits nonzero when any required physical artifact is missing.

## Evidence

- Added a shell evidence gate for physical KV260 network artifacts.
