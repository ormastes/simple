# NVMe Base-Spec Command System Test Plan

## Scope

Cover the minimum NVMe command floor needed before treating the firmware as production-oriented:
Identify, queue create/delete, Read, Write Zeroes, DSM Trim, Flush, Get/Set Features, log/format/firmware admin guards, namespace reserved-field guards, and Abort/backpressure behavior.

## Executable Evidence

- `test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl`
- `examples/09_embedded/simpleos_nvme_fw/fw_rv32/base_spec_check.spl`

## Pass Criteria

- The host-facing controller demo reports Identify, queue lifecycle, invalid queue binding, busy queue deletion rejection, teardown, SMART, and power-cycle markers.
- The rv32-compatible scalar command floor reports one PASS marker per required command family.
- Any missing runner, nonzero command result, or missing marker fails the system spec.
