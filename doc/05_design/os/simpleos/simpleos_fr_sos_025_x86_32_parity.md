# FR-SOS-025 x86_32 OS Parity Design

**Feature request:** `FR-SOS-025`
**Status:** Acceptance criteria implemented; x86_32 remains documented
separately from the x86_64 full OS lane until broader release verification
promotes it.

## Scope

FR-SOS-025 tracks the work required before the `x86_32`/`i686` SimpleOS target
can be described as a full OS lane. The current full OS acceptance lane remains
`x86_64`. The `x86_32` lane is intentionally limited to boot/probe validation
until its live build, trap, process, filesystem, and shell paths pass the same
observable acceptance level.

## Current Boundary

The `x86_32` target owns real HAL modules under `src/os/kernel/arch/x86_32/`
for boot metadata, serial console, CPU primitives, paging, interrupt/PIC
models, timer, task context construction, trap marshalling, and the future
ring-3 entry bridge. These modules are valid implementation pieces, but they do
not by themselves prove full OS parity.

The accepted boot/probe evidence is:

- target metadata and aliases use `qemu-system-i386`, `i686-unknown-none`,
  `pc`, and `qemu32`;
- the gated live probe is
  `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 bin/simple test test/03_system/simpleos_x86_32_boot_probe_live_spec.spl`;
- the live probe may only close when an i686-capable freestanding
  native-build lane produces the probe kernel and QEMU serial output reaches
  `[probe browser-x86] spl_start`.

## Full OS Promotion Criteria

Promote `x86_32` from boot/probe to full OS only after all of these are true:

- live boot/probe passes on the current toolchain and QEMU;
- paging, interrupt, timer, context, and syscall entry paths have common HAL
  contract coverage and a live trap-entry path;
- process creation, `brk`, reboot, process diagnostics, and shell smoke tests
  pass without x86_64-only helpers;
- filesystem-backed app execution has a FAT32/NVMe or equivalent QEMU lane at
  the same acceptance level as the x86_64 desktop/app lane;
- public docs and runners continue to say that `x86_64` is the full OS lane
  until every item above is proven.

## 2026-05-29 Acceptance Evidence

The live x86_32 QEMU spec now covers boot, `int 0x80`, installed early syscall
dispatch, process/shell smoke, and an equivalent FAT32 initrd filesystem app
lane. The filesystem lane passes a FAT32 image as a Multiboot module, verifies
staged `HELLOSMF`/`BROWSMF` x86_32 payloads, and gates app spawn pids on those
payloads through the i386 syscall bridge.

Command:
`SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/03_system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`

Result: `5/5` live checks passed.

Catalog scenario:
`SIMPLE_LIB=src bin/simple os test --scenario=x86_32-initrd-fat32-smf`

Result: passed with `[x86_32 fs] app execution ok` and `TEST PASSED`.

## Documentation Rule

Any SimpleOS architecture, build, or guide document that lists `x86_32` beside
`x86_64` must preserve this distinction:

- `x86_64`: full OS lane;
- `x86_32`/`i686`: boot/probe and HAL-development lane until FR-SOS-025 closes.

This rule prevents metadata support, source presence, or gated tests from being
mistaken for full OS parity.
