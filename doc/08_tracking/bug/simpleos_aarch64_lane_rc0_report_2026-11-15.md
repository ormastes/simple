# aarch64 Limine kernel build / EFI boot check reported rc 0 with no artifact

- **Status:** verification-pending
- **Found:** 2026-11-15

## Report
Two runs were reported as exiting with rc 0 while producing nothing:
`check-simpleos-arm64-efi-real-firmware-boot.shs`, which printed
`ERROR — nothing was checked`, and `build-simpleos-aarch64-limine-kernel.shs`,
which left no ELF.

## Confirmed behaviour
Each script was run directly in WSL Ubuntu-24.04 with its exit status read on
the next line:
- The boot check exits **2** (`oops`, line 70).
- The kernel build exits **1** (`set -e`, plus the guards at lines 65 and 67).

The scripts do not fail open. The rc 0 came from the caller recipe
`wsl -d Ubuntu-24.04 -- bash -lc '...; echo rc=$?'`, where the outer shell
expands `$?` and other `$VARS` before the inner bash runs. For example,
`bash -lc 'false; echo rc=$?'` prints `rc=0`. When you need an exit status
through `wsl`, put the commands in a script file and run that file.

## Prevention
`test/01_unit/os/aarch64_limine_lane_fail_closed_test.shs` covers four cases.
In three of them a fake compiler exits 0 with no ELF, exits 1, or writes an
empty ELF. In the fourth, the boot check runs without a kernel. All four must
exit non-zero, and the test fails if any of them exits 0.
