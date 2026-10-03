# Default QEMU lane parity

**Manual draft; current execution and SPipe generation TEST_BLOCKED.**
Source: `test/01_unit/os/qemu_lane_projection_v1_spec.spl`.

Resolve the six catalog defaults: x86_64, x86_32, ARM64, ARM32, RV64 and RV32.
Read memory and CPU choices through the shared resource owner. Seal each plan
and compare its executable and complete argv with the established runner.
Check the required display, device, firmware and filesystem arguments.

Negative scenarios reject an unknown lane option, required native acceleration
absent from the compatibility command, and generic binding that would discard
lane devices. Additional cases inspect structured initrd and NVMe wiring.

The 2026-10-01 source update restores explicit `-smp` parity and correct GiB
conversion. It is not executed parity proof. Resume with the exact admitted
runtime commands in `doc/03_plan/sys_test/simpleos_sealed_cli_dispatch.md`;
retain the complete/zero-stub generation receipt before claiming admission.
