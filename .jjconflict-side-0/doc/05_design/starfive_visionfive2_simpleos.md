<!-- codex-design -->
# StarFive VisionFive 2 SimpleOS detail design

## Data and interfaces

- Target: `riscv64-starfive-jh7110`; board: `starfive-jh7110`.
- Image: `build/os/starfive-jh7110/simpleos.elf`; receipt beside it.
- Link: `0x40200000`; conservative MVP RAM: `0x40000000` through the minimum supported 2 GiB board range, with kernel/heap bounds validated.
- UART: DesignWare 8250 at `0x10000000`, 32-bit register accesses, shift 2, firmware configured, 115200 8N1, THRE-polled writes.
- Boot markers: `STARFIVE entry`, `STARFIVE console-ready`, `STARFIVE filesystem-ready`, `STARFIVE shell-ready`.
- Root builder: `starfive_mount_packaged_root() -> Result<text, text>` seeds `bin`, `etc`, and `README.txt`, mounts the driver, then verifies public `g_vfs_readdir("/")`.

## Build and receipt

The build wrapper selects a self-hosted compiler using the repository helper, invokes bounded native-build with the StarFive entry/linker, validates ELF64/RISC-V/entry address, and atomically writes schema, hashes, compiler provenance, exact arguments, board/DTB contract, git revision, and timestamp. It never uses the Rust seed implicitly.

## Tigard and U-Boot

Detection resolves exactly one `0403:6010` device and its interface-specific stable paths; it never assumes tty numbering. UART capture uses channel A with timeout. JTAG uses channel B, the actual EEPROM descriptor override, a repository JH7110 TAP config, scan-only default, and trap-based driver restoration. The U-Boot flow accepts only the fixed RAM-load/hash/execute vocabulary and rejects flash-write tokens.

## Shell flow

After memory/module/service initialization, StarFive mounts the packaged root. Only a successful public VFS listing emits `filesystem-ready`. The existing serial shell authentication remains. The harness logs in, sends `ls`, times response, and requires all three entries from `_shell_ls -> g_vfs_readdir`.

## Error classification

- exit 0 plus complete receipt: PASS;
- missing/ambiguous adapter, UART silence, or uncorrected all-ones JTAG: BLOCKED (exit 2);
- malformed receipt, wrong TAP, observed boot fault, missing marker, static listing, timeout, or destructive command: FAIL (exit 1).
