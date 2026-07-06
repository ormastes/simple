# NVMe Base-Spec Command System Spec

This manual mirrors `test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl`.

The spec runs the host-facing NVMe controller demo and the rv32-compatible scalar command floor. It asserts the must-have NVMe baseline: Identify, IO queue create/delete, invalid queue guards, Read, Write Zeroes, DSM Trim, Flush, Features, namespace reserved-field guards, logs, Format NVM, firmware command guards, and Abort/backpressure behavior.

The test is fail-closed: process failures or missing PASS markers fail the scenario.

Current limitation: this spec proves the host model and scalar rv32-compatible
command floor. It does not claim rv32 ELF/QEMU production boot proof while
`doc/08_tracking/bug/nvme_rv32_firmware_build_timeout_2026-07-05.md` remains
open.
