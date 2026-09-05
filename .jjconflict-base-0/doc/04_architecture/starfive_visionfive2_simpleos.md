<!-- codex-design -->
# StarFive VisionFive 2 SimpleOS architecture

## Decision

Add a separate `riscv64-starfive-jh7110` target capsule. It reuses RV64GC compiler/runtime and S-mode services but owns board entry, memory/linker contract, firmware-preserved UART policy, deterministic MVP root, build receipt, and Tigard/U-Boot tooling. Existing QEMU and FPGA targets remain siblings and are not parameter-overwritten.

## Layering

1. **Platform catalog:** declares a U-Boot+DTB board bundle, `0x40200000` load/entry, board adapter, required boot markers, and artifact path.
2. **Board contract:** `starfive-jh7110` hardening row supplies RV64GC/Sv39, RAM base `0x40000000`, UART `0x10000000`, and the physical wrapper.
3. **Architecture entry:** `starfive/entry.spl` preserves `a0`/`a1`, establishes stack/BSS, validates the DTB handoff, initializes conservative JH7110 memory, and delegates shared kernel services. Its adjacent `starfive/boot` runtime isolates the board closure from QEMU boot runtime discovery.
4. **Console provider:** the RV64 UART owner accepts a platform contract. StarFive uses DesignWare 8250 word accesses with shift 2 and preserves firmware-configured 115200 8N1; QEMU retains byte accesses and divisor programming.
5. **Filesystem capsule:** an immutable packaged-root manifest is mounted before the shell. Public VFS `readdir` resolves that manifest, so CLI `ls` has no static listing path.
6. **Host orchestration:** bounded scripts detect Tigard, build and receipt the image, capture UART, scan JTAG, and drive RAM-only U-Boot commands. Hardware absence is BLOCKED; observed target failure is FAIL.

## Critical invariants

- Never call `rt_riscv_qemu_*` from the StarFive entry.
- Preserve the incoming DTB pointer and validate FDT magic before claiming it.
- Do not reprogram JH7110 UART clock/divisor in the MVP.
- Never accept all-zero/all-one or non-`0x07110cfd` JTAG identity.
- Normal tooling contains no QSPI/MMC/NAND write, erase, or `saveenv` operation.
- FTDI interface B is rebound on every exit path when the tool unbound it.
- `ls /` reads the mounted VFS and exposes `bin`, `etc`, and `README.txt`.

## Known implementation defects claimed by this feature

The generic RamFs compatibility methods and mount-table directory path are fixed at their owning layers. Live RV64 evidence additionally showed nested mutable RamFs inode state does not survive this freestanding backend closure, so the read-only board root uses an immutable packaged VFS manifest. The shell remains generic and contains no hardcoded listing.

## Risks

The tested U-Boot `bootelf -s` uses an application ABI rather than OpenSBI-style `a0`/`a1`. The reviewed board shim validates FDT magic at firmware address `0x42200000` before binding hart 1 and fails closed otherwise; `bootelf -p` is rejected because this U-Boot faults in its program-header loader.
