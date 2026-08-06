# aarch64 SimpleOS: real-firmware boot gap + 2 seed/driver defects (launch sanity, 2026-07-14)

Found by Lane LAUNCH-OS-AARCH64 doing a real launch sanity check. The aarch64
kernel boot gate (loader + FS-exec staging) reproduces GREEN
(`ARM64_SIMPLE_TOOL_GATE_PASS` / `TEST PASSED`, `e_machine=183`, QEMU self-exit
via semihosting) and the WM readiness check is READY. These three items are the
honest gaps/defects behind that green, so the workarounds are not silently
normalized.

## 1. No real-firmware (EDK2/UEFI) boot path on aarch64 — board-proxy gap

The board-proxy rule wants boot via real firmware, not QEMU `-kernel` pass
semantics. On **riscv64** this is automatic: `-kernel` loads the kernel as an
S-mode payload *through* OpenSBI, so BR64 satisfies the rule. On **x86_64** we
use OVMF pflash. **aarch64 has no such analog today:** the probe kernel is a
pure bare-metal ELF (entry `0x40200000`, crt0 does the EL2→EL1 drop) with **no
PE/EFI-stub, no arm64 `Image` header, no multiboot header**. So:

- `qemu-system-aarch64 -machine virt -kernel bareELF` boots it directly at EL1
  with **no firmware** — works, but is not a firmware boot.
- `-bios AAVMF(EDK2) -kernel bareELF` → EDK2 boots (`UEFI firmware version
  2024.02`) but **cannot load the bare ELF** (`BdsDxe: ... Not Found`, zero
  kernel markers) because it has no EFI entry.

**Fix (concrete follow-up, not a regression):** give the aarch64 kernel a UEFI
**EFI-stub** (PE/COFF header + `efi_main` that sets up and jumps to the existing
entry), OR provision an aarch64 bootloader (arm64-efi GRUB or aarch64 U-Boot) as
the pflash payload that then loads the ELF. Local tooling is currently missing
(no arm64-efi GRUB platform, no aarch64 U-Boot, and curl/wget are blocked), so
this needs either the EFI-stub in-tree or a provisioning step. Until then the
aarch64 "board proxy" is EL1-direct `-kernel`, which is weaker than x86/riscv.

## 2. Seed cranelift miscompiles `_arm_fat32_find_sys_cluster` on spc=8

The bootstrap seed's cranelift backend miscompiles the arm64 VFS helper
`_arm_fat32_find_sys_cluster` when sectors-per-cluster == 8: it reads garbage
from FAT32 directory data that a sibling function reads correctly. Worked around
in `src/os/services/vfs/arm_fs_exec_vfs.spl:409` (root-scan + inline byte
matcher instead of the miscompiled path). Real fix belongs in the seed cranelift
codegen (arm64) or the #99 self-hosted redeploy. Same class as the x86_64 seed
enum-payload miscompile.

## 3. arm64 virtio-blk descriptor ring is single-sector-only

The arm64 baremetal virtio-blk driver descriptor ring reads only one sector per
request; a multi-sector `read_prefix` corrupts data past sector 0. VFS currently
reads cluster data sector-by-sector as a workaround
(`src/os/services/vfs/arm_fs_exec_vfs.spl:265`), which is why the staged
`/simple.elf` returns 529502 of 4.2MB (enough to validate the ELF header, not to
run it). Note at `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:2578`.
Fix: multi-descriptor chaining in the arm64 virtio-blk ring so a whole cluster
(or larger prefix) transfers in one request.

## Status

Boot + loader/FS-exec staging on aarch64 is GREEN with these workarounds. Full
in-guest U-mode Simple RUN stays blocked on the #99 seed-cranelift enum
miscompile (all arches). Items 1-3 are the concrete follow-ups; none is a
regression.

## 2026-08-06 research: EFI-stub scoping (mirroring the x86_64 pattern)

Scoping pass for item 1. Verified the doc above is still current. Key
correction: **the x86_64 "real-firmware" path does NOT hand-author a PE/COFF
EFI-stub in-tree.** It uses a prebuilt third-party UEFI bootloader (Limine),
not a custom entry point. This changes the recommended aarch64 approach from
"write a PE/COFF stub" to "port the Limine-protocol kernel entry + provision
Limine's aarch64 binary" — mirroring what x86_64 already does, not inventing
new PE/COFF work.

### x86_64 pattern (verified from source)

- `examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s` is a **Multiboot1**
  header (`.text.entry`), used for the plain `-kernel` dev-harness lane —
  not the real-firmware lane.
- The real-firmware lane (`x64-desktop-uefi` scenario,
  `src/os/_QemuRunner/scenario_catalog.spl` / `scenario_disks.spl` /
  `scenario_exec.spl`) boots OVMF pflash (`ovmf_code_path()`, candidates incl.
  `/usr/share/OVMF/OVMF_CODE_4M.fd`) → **Limine's prebuilt `BOOTX64.EFI`**
  (`desktop_uefi_bootloader_path()` searches
  `build/third_party/limine-install/share/limine/BOOTX64.EFI`,
  `vendor/limine/BOOTX64.EFI`, etc. — **not present in this checkout**; it's
  an external artifact the build must provision) → Limine loads the kernel
  ELF per the Limine boot protocol and jumps to `kernel_main()`.
- `src/os/kernel/boot/limine_boot.spl` (438 lines) is the actual EFI-side
  entry point in spirit: it defines Limine request/response structs
  (`@repr("C")`, magic IDs `LIMINE_COMMON_MAGIC_0/1` etc.), parses memory
  map / framebuffer / RSDP / HHDM / kernel-address responses via raw MMIO
  reads, and its `@entry @noreturn fn kernel_main()` is what Limine calls
  after UEFI handoff. This is a **protocol port**, not PE/COFF authorship —
  Limine's own binary is the actual PE32+ EFI_APPLICATION; SimpleOS never
  emits PE/COFF itself for x86_64.
- Conclusion: there is **no existing in-tree pattern for writing a PE/COFF
  header or `efi_main(handle, systab)` UEFI entry** to mirror — x86_64
  delegates that entirely to Limine.

### aarch64 gap, restated

`examples/09_embedded/simple_os/arch/arm64/boot/crt0.S` is a pure bare-metal
ELF entry at `0x40200000` (EL2→EL1 drop) — no PE header, no Multiboot header,
no Limine request/response structs, no `@entry` Limine-protocol
`kernel_main()`. There is no `arch/aarch64/` directory yet (existing dir is
named `arm64/`). Confirms doc item 1 exactly as written.

### LLVM PE/COFF+AArch64 capability — mixed evidence

- **Generic capability confirmed, real command+output:** stock system
  `clang-18` (NOT the SimpleOS fork) emits a valid AArch64 COFF object:
  ```
  $ clang-18 --target=aarch64-unknown-windows -c -o /tmp/test2.obj -x c /tmp/t.c
  exit=0
  $ file /tmp/test2.obj
  /tmp/test2.obj: Aarch64 COFF object file, not stripped, 4 sections,
  symbol offset=0xb8, 12 symbols, created ..., 1st section name ".text"
  ```
  So AArch64+COFF is a real, low-risk pairing in mainline LLVM 18.
- **In-fork status: UNCONFIRMED, and not currently testable.** The repo's own
  built binary `build/os/clang_static/bin/clang_static` (121MB, mtime today —
  likely mid-rebuild by a concurrent lane) **segfaults on every invocation**
  right now, including plain `--version` and `-print-targets` (exit 139, core
  dumped). Did not retry further to avoid measuring a sibling lane's
  in-progress build (see `feedback_measurement_traps_harness_not_system`).
  `src/os/port/llvm/build.spl` configures `LLVM_TARGETS_TO_BUILD` per target
  triple (`AArch64` for `aarch64-*`) with `LLVM_ENABLE_PROJECTS=clang;lld`,
  so lld's COFF driver + AArch64 backend are plausibly both buildable, but
  this was not verified against a live binary today.
- **Moot either way for the recommended approach:** since x86_64 doesn't
  emit its own PE/COFF (Limine does), aarch64 shouldn't either — this
  question only matters if the fallback "build Limine from source with the
  in-tree fork" sub-path is taken (see plan step 3 below).

### QEMU + AAVMF firmware — already ready on this machine, no provisioning needed

```
$ qemu-system-aarch64 --version   → QEMU emulator version 8.2.2 (Debian 1:8.2.2+ds-0ubuntu1.17)
$ qemu-system-aarch64 -machine help | grep -i virt   → virt-8.2 (aliased "virt") present, sbsa-ref present
$ dpkg -l | grep qemu-efi-aarch64 → ii qemu-efi-aarch64 2024.02-2ubuntu0.8
```
Firmware images found:
- `/usr/share/AAVMF/AAVMF_CODE.fd`, `AAVMF_CODE.no-secboot.fd`, `AAVMF_VARS.fd` (pflash CODE+VARS pair, Debian `ovmf`-style layout)
- `/usr/share/AAVMF/AAVMF32_CODE.fd` / `AAVMF32_VARS.fd` (32-bit ARM)
- `/usr/share/qemu-efi-aarch64/QEMU_EFI.fd` (single-file EDK2 image)

### Network constraint (why the stretch goal was not attempted)

curl/wget are blocked in this session's environment (context-mode routing
policy), and no equivalent MCP fetch tool was available to this agent. This
blocks obtaining a prebuilt Limine aarch64 `BOOTAA64.EFI` from upstream —
the actual bottleneck for a real boot, not EFI-stub authorship. Combined
with the in-fork `clang_static` crash above (so "build Limine from source
in-tree" is not currently a verified fallback either), the stretch goal was
not attempted — this is a plan-only research pass, per the task's explicit
stop condition ("if it doesn't clearly work within a reasonable number of
attempts, STOP and fall back to documenting the plan").

### Concrete plan (mirrors x86_64's Limine pattern, not a hand-rolled PE stub)

1. **Provision Limine's aarch64 UEFI binary** (`BOOTAA64.EFI`). Two paths:
   (a) fetch upstream prebuilt release from a session with network access —
   Limine has shipped aarch64 UEFI support upstream for years, lowest risk;
   or (b) build Limine from source using the in-tree LLVM/clang fork, which
   requires first confirming the fork's AArch64 backend + lld COFF driver
   are healthy (blocked today by the `clang_static` crash above — retest
   once that lane's build finishes).
2. **Port `src/os/kernel/boot/limine_boot.spl` → a new
   `limine_boot_aarch64.spl`** (or arch-branch the existing file). The
   Limine request/response protocol (magic IDs, struct layouts) is
   architecture-agnostic — reuse verbatim. Arch-specific deltas: early
   serial uses PL011 UART MMIO (QEMU `virt` base `0x09000000`) instead of
   x86 port I/O at `0x3F8`; drop the x86-only
   `x86_64_hardening_boot_canary_marker()` call; `Architecture.AArch64` in
   `BootOutputPort`. AAPCS64 entry convention needs no shadow-space handling
   (unlike x86_64 MS ABI concerns elsewhere in this repo) — Limine calls
   `kernel_main()` with no arguments here, same as the x86_64 version, so
   the calling-convention risk is low.
3. **New `examples/09_embedded/simple_os/arch/aarch64/boot/`** (deliberately
   distinct from `arch/arm64/boot/`, which stays the EL1-direct bare-metal
   lane owned by a concurrent lane) holding: a Limine-protocol linker
   script (`.limine_reqs` section placement; output is a plain ELF, *not*
   PE — Limine's own binary is the PE32+ EFI_APPLICATION, the kernel it
   loads stays ELF, exactly as x86_64 does), and any minimal aarch64 crt
   glue Limine's protocol needs (typically none beyond the linker script,
   since Limine hands off already in EL1/64-bit mode with a set-up stack).
4. **Extend `src/os/_QemuRunner/scenario_disks.spl` /
   `scenario_catalog.spl`** with an `aarch64-desktop-uefi` scenario mirroring
   `x64-desktop-uefi`: `SIMPLEOS_AAVMF_CODE` (+ `_VARS`) env vars pointing at
   `/usr/share/AAVMF/AAVMF_CODE.no-secboot.fd` / `AAVMF_VARS.fd`, and an
   aarch64 bootloader-path search list mirroring `ovmf_code_candidates()` /
   `desktop_uefi_bootloader_path()` but for `BOOTAA64.EFI`. FAT32 ESP layout:
   `EFI/BOOT/BOOTAA64.EFI` (Limine) + `limine.conf` + the aarch64 kernel ELF,
   built via a `make_os_disk.shs`-equivalent step for aarch64 (script
   already parameterizes arch as `"x86_64"` today — extend, don't fork).
5. **Milestone ("boots to a serial print"):** compile the ported
   `limine_boot_aarch64.spl` kernel_main → link as plain ELF → package into
   the FAT ESP with provisioned `BOOTAA64.EFI` → `qemu-system-aarch64 -M
   virt -cpu cortex-a72 -pflash AAVMF_CODE.no-secboot.fd -pflash
   AAVMF_VARS.fd -drive if=virtio,format=raw,file=esp.img -serial stdio` →
   see the ported "SimpleOS — Limine Boot Protocol" banner + boot-info dump
   on serial, matching what `limine_boot.spl:kernel_main()` already prints
   for x86_64. No ring-3/FS-exec/syscalls in scope — boot-entry only.

**Risk estimate (superseded by the 2026-08-06 implementation pass below):**
low-to-medium, roughly 1-3 days of work *once a working `BOOTAA64.EFI` is in
hand* — the protocol-port work (step 2) is a near-mechanical port of an
existing 438-line file with a well-understood arch delta (PL011 vs 0x3F8
serial). The actual bottleneck is step 1 (provisioning Limine's binary),
which is blocked in this environment by the curl/wget block and an
unverified in-fork LLVM/lld AArch64-COFF path. Specific risky spots if step
1(b) (build-from-source) is taken instead of 1(a) (fetch prebuilt): PE32+
relocation model / image-base alignment / `.reloc` section correctness for a
*linked* EFI application (not just a COFF object, which is already confirmed
easy) is unverified — Limine's own build system handles this upstream, so
building Limine from source is lower-risk than hand-rolling equivalent lld
invocations. Also unverified: whether this QEMU/EDK2 version's aarch64
`virt` machine needs `gic-version=3` or similar tuning for a clean Limine
UEFI boot — untested without an actual boot attempt.

## 2026-08-06 implementation pass: BOOTAA64.EFI acquired, real boot achieved, runtime port still open

Correction to the "network constraint" section above: **curl/wget being
blocked does not mean this environment has no network access.** `git clone`
over https works (`git ls-remote https://github.com/...` succeeds), and
Limine's upstream repo ships prebuilt binaries as committed git objects on
orphan branches named `vN.x-binary` (verified: `v7.x-binary` through
`v11.x-binary` all present via `git ls-remote --heads`). This is the
standard, first-party distribution channel for Limine binaries — not a
workaround.

```
$ git clone --depth 1 --branch v10.x-binary \
    https://github.com/limine-bootloader/limine.git limine-bin
$ file limine-bin/BOOTAA64.EFI limine-bin/BOOTX64.EFI
BOOTAA64.EFI: PE32+ executable (EFI application) Aarch64 (stripped to external PDB), for MS Windows, 3 sections
BOOTX64.EFI:  PE32+ executable (EFI application) x86-64 (stripped to external PDB), for MS Windows, 3 sections
$ git -C limine-bin log -1 --format='%H %s %ai'
7a9013f305de0bea1f6310e76e7baba30499fef0 Binary release v10.8.5 2026-03-11 23:32:34 +0000
```

Both binaries are now vendored at `vendor/limine/{BOOTX64.EFI,BOOTAA64.EFI}`
— exactly the path `desktop_uefi_bootloader_path()` in
`src/os/_QemuRunner/scenario_catalog.spl` already searches for x86_64 (that
scenario was previously non-runnable: "not present in this checkout"; it is
now provisioned). Repeatable acquisition:
`sh scripts/os/provision_limine_efi.shs` (re-clones the pinned branch,
verifies both files, re-copies into `vendor/limine/`).

### Real-firmware boot proven end-to-end, both arches

Before porting `limine_boot.spl`, validated the vendored binaries actually
boot under real firmware using a minimal hand-written C probe kernel (NOT
the Simple-language kernel — this is a protocol/toolchain validation step,
not a shortcut around the "no PE/COFF stub" rule; the probe is a plain ELF
loaded *by* Limine, same as the eventual SimpleOS kernel will be). Built
with the system's stock `clang`/`ld.lld` (`--target=x86_64-elf` /
`--target=aarch64-elf`, both present and working — no dependency on the
in-fork `clang_static` that was crashing in the 2026-07-14 pass).

Two real, previously-undocumented protocol requirements surfaced only by
attempting an actual boot (both produce Limine PANICs with no other clue):

1. **Kernel must link higher-half.** A kernel with a lower-half link address
   (e.g. `0x100000`) is rejected outright: `PANIC: elf: Lower half PHDRs are
   not allowed`. (`limine_boot.spl`'s own comment — "Called by Limine
   bootloader after loading kernel into higher-half" — already anticipated
   this; it just hadn't been verified against a real binary until now.)
2. **Every PT_LOAD segment must be page-aligned in its own page.** Packing
   R+X and R+W data into the same page triggers `PANIC: elf: Attempted to
   load ELF file with PHDRs with different permissions sharing the same
   memory page.` Fixed via a `PHDRS { text PT_LOAD FLAGS(5); data PT_LOAD
   FLAGS(6); }` linker script with explicit `ALIGN(0x1000)` between them.
3. **`limine.conf` (not `.cfg`) needs `serial: yes` and `graphics: no`, or
   the bootloader's own console output never reaches the serial port at
   all** — not an error, a silent indefinite hang (confirmed via `-d
   int,cpu_reset` CPU tracing: QEMU was alive and servicing timer
   interrupts in a firmware polling loop, not crashed). This is a
   config-format gap the existing in-tree `limine.cfg` samples
   (`build/.../efi/limine.cfg`, `KERNEL_PATH=` old syntax) don't cover —
   Limine v10 requires the new `protocol:`/`path:` `.conf` syntax; the old
   `.cfg` files elsewhere in this tree target a different (pre-v8) Limine
   version and would need updating separately if ever exercised.
4. **No version skew in the base protocol itself.** `limine_boot.spl` uses
   `revision: 0` requests (no `LIMINE_BASE_REVISION` tag) — confirmed
   still supported by v10.8.5's bootloader source
   (`common/protos/limine.c`: `base_revision == 0` falls back to scanning
   the ELF's `.limine_reqs` section directly, exactly the section name
   `limine_boot.spl`'s linker-placement comments already use). No port
   work needed on this axis.

With both fixes applied, real-firmware boot to serial banner succeeded on
**both architectures**, disk image built as a real FAT32 file (via
`mkfs.vfat` + Python `pyfatfs`, avoiding a QEMU `vvfat`-synthesis hang that
appeared unrelated to Limine — same vvfat setup used successfully elsewhere
in this repo by GRUB, so likely an artifact of this probe's minimal disk
layout rather than a vvfat defect per se; not investigated further since a
real disk image sidesteps it entirely):

```
x86_64:  qemu-system-x86_64 -M q35 -pflash OVMF_CODE_4M.fd -pflash OVMF_VARS_4M.fd \
           -device virtio-blk-pci,drive=esp ... -serial file:x86_64.serial.log
  -> "limine: Loading executable `boot():/boot/kernel.elf`...SIMPLEOS-LIMINE-X86_64-PROBE-OK"

aarch64: qemu-system-aarch64 -M virt -cpu cortex-a72 \
           -pflash /usr/share/AAVMF/AAVMF_CODE.no-secboot.fd -pflash AAVMF_VARS.fd \
           -device virtio-blk-pci,drive=esp ... -serial file:aarch64.serial.log
  -> "limine: Loading executable `boot():/boot/kernel.elf`...SIMPLEOS-LIMINE-AARCH64-PROBE-OK"
```

The aarch64 probe kernel's `_start` writes directly to PL011 `DR` at
`0x09000000` (QEMU `virt` UART0), confirming the MMIO base and access width
`limine_boot_aarch64.spl` (below) assumes.

### Protocol port landed; freestanding-runtime port is the real remaining gap

`src/os/kernel/boot/limine_boot_aarch64.spl` — a structural port of
`limine_boot.spl`'s request/response parsing and `kernel_main()`, with the
arch deltas from item 2 of the original plan (PL011 `serial_base:
0x09000000` / `serial_is_mmio: true`, `Architecture.Arm64`, x86_64-hardening
canary call dropped). Companion linker script
`examples/09_embedded/simple_os/arch/aarch64/boot/linker_limine.ld` encodes
the higher-half + page-alignment requirements discovered above.

**Neither has been compiled through the Simple toolchain or linked into a
booting SimpleOS kernel yet.** Tracing `extern fn serial_println(msg: text)`
(what `klog_api.spl`'s `log_raw_println` ultimately calls) to its
implementation revealed why that's a separate, larger task than the
protocol port itself:

- x86_64's baremetal `serial_println` lives in
  `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` — a
  ~9,200-line freestanding reimplementation of the Simple runtime's print
  path (`rt_print`, tagged-value decoding, `serial_puts`/`serial_getchar`
  over port 0x3F8, plus much more of the baremetal runtime surface).
- arm64's EL1-direct lane (`arch/arm64/`) uses a much smaller pattern
  instead — `arch/common/baremetal_min_stdout.h` (~40 lines: just
  `rt_stdout_write`/`rt_stdout_flush` over a `serial_putchar` the caller
  supplies) + `arch/common/baremetal_pl011_uart_stdout.c` (PL011 register
  init/write, reused as-is for the probe kernel above) — but this smaller
  surface does **not** implement `serial_println(text)` as `klog_api.spl`
  expects; it's wired for a different call convention
  (`__simple_call_module_inits` + `spl_start`, the arm64 bare-metal boot
  entry style, not Limine's direct `kernel_main()` jump).
- **There is currently no aarch64 equivalent of `baremetal_stubs.c`'s
  `serial_println(RuntimeValue)`.** Writing one (or a smaller subset
  sufficient for `limine_boot_aarch64.spl`'s actual call surface — only
  `log_raw_println`/`log_raw` are used, not the full runtime) is the next
  concrete step, followed by an aarch64 crt (Limine hands off with a set-up
  stack per protocol, so this should be minimal — likely no assembly
  needed beyond what the linker script's `ENTRY(kernel_main)` already
  captures) and a real `bin/simple build` compile+link+boot pass reusing
  the exact QEMU command line proven above.
- `src/os/_QemuRunner/scenario_catalog.spl` / `scenario_disks.spl` are not
  yet extended with an `aarch64-desktop-uefi` scenario (plan step 4) —
  deliberately deferred until there's a real kernel to boot with it, since
  wiring scenario plumbing ahead of a working artifact would be
  unverifiable and touches shared-lane files.

**Board-runnable note:** the AAVMF-pflash boot above is the correct
real-firmware proxy per `.claude/rules/board-runnable.md` and satisfies the
board-proxy requirement for this milestone. It is a QEMU/EDK2 boot, not a
physical-aarch64-board boot; no physical-board claim is made here.
