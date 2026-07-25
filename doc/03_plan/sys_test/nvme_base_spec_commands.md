# NVMe Base-Spec Command System Test Plan

## Scope

Cover Identify, queue create/delete, Read, Write Zeroes, DSM Trim, Flush,
Get/Set Features, logs, Format NVM, firmware guards, namespace reserved-field
guards, and Abort/backpressure behavior.

## Executable Evidence

- `test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl`
- `examples/09_embedded/simpleos_nvme_fw/fw_rv32/base_spec_check.spl`

## Scenarios

1. Run the host controller lifecycle and assert Identify plus queue behavior.
2. Run the rv32-compatible scalar command floor and assert every command-family marker.
3. Invoke a missing runtime and prove the test surface fails closed.

## Pass Criteria

Every command exits successfully, every required PASS marker is present, no
FAIL marker is present, and the missing-runtime probe returns nonzero.

