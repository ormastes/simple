# SimpleOS on StarFive VisionFive 2

This lane targets `riscv64-starfive-jh7110` and enters supervisor mode through
the board's existing OpenSBI/U-Boot firmware. It is a RAM-only bring-up path:
normal tooling must not issue QSPI, eMMC write, erase, NAND, or `saveenv`
commands.

The JH7110 scan chain exposes two TAPs with ID `0x07110cfd`: the E24 monitor
core first and the U74 application complex second. SimpleOS uses U74 hart 1;
targeted OpenOCD operations must select `jh7110.u74_hart1`, not the first TAP.

## Tigard wiring and identity

The admitted adapter is FTDI `0403:6010`, serial `tiBMLHE7`, with EEPROM product
`port A:Serial  port B:JTAG`. Channel A is UART at 115200 8N1; channel B is
JTAG. Scripts resolve stable `/dev/serial/by-id` identities and sysfs interface
metadata, never fixed tty numbers. JH7110 UART0 uses GPIO5 TX and GPIO6 RX;
connect grounds and the Tigard voltage reference to the powered target.

Run the canonical live workflow with:

```sh
scripts/os/run_simpleos_starfive_jh7110.shs
```

The workflow detects Tigard, builds the admitted ELF and receipt, loads only to
RAM through U-Boot, retains one stateful UART transcript, observes ordered boot
markers, logs into the serial shell, and runs `ls /`. A passing listing is
produced by the mounted VFS and contains `bin`, `etc`, and `README.txt`.

## Failure meaning

- `starfive_status=blocked` with exit 2 means a prerequisite is unavailable:
  adapter ambiguity, UART silence, all-zero/all-one JTAG, or missing admitted
  compiler. It is not PASS.
- Exit 1 means observed failure: wrong TAP (`0x07110cfd` expected), malformed
  evidence, boot failure, forbidden flash vocabulary, or restoration failure.
- PASS requires exact compiler/image/linker hashes, entry/load `0x40200000`,
  validated preserved DTB, ordered entry/console/filesystem/shell markers, real
  `ls /` output, bounded timings, transcript paths, and restored FTDI state from
  the same run.

Current local evidence on 2026-08-16 proves bounded RAM read/write access: the
checker saved the word at `0x48000000`, wrote and read back `0x53464a54`,
restored the original word, resumed U74 hart 1, and rebound Tigard channel B.
The provenance-admitted pure-Simple Stage 3 compiler builds the board ELF. Live
acceptance reaches entry, console, filesystem, and shell markers, and `ls /`
returns `/bin`, `/etc`, and `/README.txt` through the mounted VFS.

JH7110 UART0 is DesignWare 8250-compatible at `0x10000000`, using 32-bit MMIO
accesses and register shift 2. QEMU's byte-wide 16550 provider is not
interchangeable even though its base is identical. A live probe read LSR
`0x60` at `0x10000014` and emitted one byte through a 32-bit THR write. The
StarFive runtime therefore preserves firmware configuration and uses words.

JTAG `load_image` plus `verify_image` proves that ELF segments reached RAM; it
does not prove the OpenSBI/U-Boot handoff. Direct PC resume is diagnostic only.
Production acceptance uses a fresh U-Boot prompt and its reviewed ELF or FIT
handoff so supervisor privilege, hart ID, DTB pointer, and interrupt state are
established together.

After SimpleOS replaces U-Boot, use
`scripts/os/starfive-jtag-sbi-reset.shs` to request an OpenSBI cold reboot. It
writes a three-instruction `ecall` trampoline only to scratch RAM, invokes SBI
SRST, restores Tigard channel B, and has been verified to reboot BootROM, DDR,
OpenSBI, peripherals, and U-Boot. Generic OpenOCD `reset run` is insufficient.

On the tested U-Boot 2021.10 build, `bootelf -p` faults while processing this
ELF's program headers. `bootelf -s 0x48000000` is the proven loader and reaches
`_start` at `0x40200000`. Because its application ABI supplies argc/argv rather
than OpenSBI's hart/FDT pair, the entry shim validates the preserved FDT magic
at `0x42200000` before binding hart 1. Missing FDT magic remains a hard stop.

## NVMe bring-up

The VisionFive 2 M.2 socket is PCIe1/domain 1. SimpleOS keeps JH7110 DT parsing,
PHY/clocks/resets, PERST, PLDA configuration and link validation in
`src/os/kernel/arch/riscv64/starfive/`; common PCI enumeration and
`src/os/drivers/nvme/` contain no StarFive constants.

The first RAM image uses `starfive_find_nvme_read_only()`. It checks link-status
bit 5 at `0x10240368`, scans only the bounded 16 MiB PCIe1 ECAM aperture, and
accepts class `01:08:02`. Its UART line reports domain, BDF, vendor/device IDs,
BARs, and `read_only=1`, or a precise link/not-found reason. It does not write
PCI config, NVMe registers, queues, partitions, or storage.

The vendor U-Boot may report `Unknown command` for `pci` and `nvme`; that is a
firmware configuration limitation, not SSD absence. NVMe model, serial,
firmware and namespace geometry require a real NVMe Identify command with DMA.
Never copy an example device ID from web documentation into an authorization
receipt.

Provisioning is intentionally separate. It requires an immutable identify
receipt bound to exact serial, NSID, capacity and image hash, rejects mounted,
in-use and boot-source devices, creates a bounded GPT partition, formats that
partition as FAT32, and mounts it at `/nvme`. PASS then requires a nonce file to
survive flush, unmount and remount with an equal hash, followed by a command-
correlated public-VFS `ls /nvme`. A password is privilege input, never storage
identity confirmation.
