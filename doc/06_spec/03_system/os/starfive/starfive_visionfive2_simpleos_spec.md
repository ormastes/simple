# StarFive VisionFive 2 SimpleOS bring-up

This manual is mirrored from `test/03_system/os/starfive/starfive_visionfive2_simpleos_spec.spl`. Use the canonical checker; do not assemble OpenOCD or U-Boot commands manually.

## Primary workflow

1. Detect Tigard and verify channel A is UART and channel B is JTAG.
2. Build the admitted `riscv64-starfive-jh7110` ELF and receipt.
3. Stage the raw ELF at `0x48000000` through JTAG, verify it byte-for-byte, then load sections with U-Boot `bootelf -s` without any flash write.
4. Observe ordered entry, console-ready, filesystem-ready, and shell-ready markers.
5. Log in and run `ls /`; require `bin`, `etc`, and `README.txt` from the mounted VFS.

Hardware absence, UART silence, or an all-ones scan is BLOCKED. Wrong identity, destructive commands, malformed evidence, or observed boot failure is FAIL.

The canonical live checker may be run as root because it temporarily unbinds
only Tigard interface B. It first requests an SBI cold reboot through a
three-instruction RAM trampoline, restores the FTDI driver, stops U-Boot
autoboot, performs the staged load, and retains all transcripts under
`build/test-artifacts/03_system/os/starfive/`.
