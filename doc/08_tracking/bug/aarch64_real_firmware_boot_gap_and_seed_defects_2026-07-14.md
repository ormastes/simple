# aarch64 SimpleOS: real-firmware boot gap + 2 seed/driver defects (launch sanity, 2026-07-14)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## 2026-08-07: aarch64 freestanding-runtime port landed, real kernel boots and logs via klog on real firmware

Milestone achieved: the **real** SimpleOS kernel (`limine_boot_aarch64.spl`,
not the probe kernel) now boots through Limine + AAVMF pflash on QEMU
aarch64 `virt` and prints a real `klog_api.log_raw_println` line over PL011
serial. Sabotage-verified (see below).

### Files landed

- `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`
  (new) — ported from `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`.
  The RV64 file turned out to be ~90% arch-agnostic C runtime shim
  (string/array/tuple/enum tagged-value helpers) with the arch delta
  confined to a handful of functions; ported the generic section verbatim
  (through `void unsafe(void) {}`, RV64's own line 1458) and dropped the
  RV64-only tail (~3000 lines: PMM, virtio-blk/input/gpu drivers, a
  `.incbin` of a RV64 FAT32 image) as out of scope for a boot-entry-only
  milestone. Arch deltas: PL011 MMIO byte-store at `0x09000000` (replacing
  the RV64 NS16550 store at `0x10000000`), a WFE spin halt
  (`rt_aarch64_wfe_spin`, replacing the x86_64-only `os.kernel.boot.cpu`
  import — see below), and no custom `_start` asm stub (Limine hands off
  with a stack already set up; RV64's stub wouldn't even assemble under
  `--target=aarch64-none-elf` since it's RISC-V asm).
- `examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl` (new) —
  thin entry wrapper. Required for two independent reasons, both discovered
  empirically by iterating real build/link failures, not from documentation:
  1. Boot-object autodiscovery (`link_objects_freestanding()` in
     `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`)
     keys off `<entry-file's-dir>/boot/`. `limine_boot_aarch64.spl` lives
     under `src/os/kernel/boot/`, so passing it directly as `--entry` would
     search `src/os/kernel/boot/boot/` (doesn't exist) and never find
     `freestanding_runtime.c`.
  2. **Entry-symbol mangling bug found and worked around**: native-build
     mangles every top-level function with its full module path
     (`src__os__kernel__boot__limine_boot_aarch64__kernel_main`), not a bare
     `kernel_main`. `ENTRY(kernel_main)` in a linker script silently
     resolves to nothing under `ld.lld` (no error — entry point just
     becomes `0x0`), and `--gc-sections` then has no GC root, discarding
     the *entire* reachable call graph and producing a "successfully
     linked" ~1 KB binary with **no `.text` section at all**
     (`readelf -S` showed only `.bss`). Found by comparing this build's
     `nm` output against a real working build. The linker only
     auto-generates a `--defsym=_start=<mangled-symbol>` /
     `--entry=_start` alias (see the `raw_start_candidate` derivation in
     `linker.rs`, ~line 2160) for a top-level function **literally named
     `_start`** in the entry file — exactly mirroring
     `examples/09_embedded/simple_os/arch/riscv64/entry.spl`'s own
     `fn _start():`. Fix: `limine_entry.spl` defines `fn _start():` which
     calls `limine_boot_aarch64.limine_aarch64_boot_main()` (the real
     kernel_main renamed), and `linker_limine.ld` now says
     `ENTRY(_start)`. **This same trap likely exists for anyone hand-writing
     a new freestanding entry `.spl` file that isn't named/structured like
     the existing riscv64/x86_64 ones** — worth a linker.rs-level warning
     when `ENTRY(kernel_main)`-style directives don't match any resolvable
     symbol, since the current silent-success-with-empty-binary failure
     mode is a genuine trap (logged here rather than fixed in the Rust seed,
     per this session's C/asm-only scope).
- `src/os/kernel/boot/limine_boot_aarch64.spl` (modified) — three fixes:
  1. Renamed `kernel_main` → `limine_aarch64_boot_main` (see above).
  2. **`use os.kernel.boot.cpu.{halt_loop}` was wrong for this arch** —
     that module's `halt_loop()` calls `rt_cli()`/`rt_hlt()`, x86-only
     `cli`/`hlt` instructions with no aarch64 meaning, and importing the
     module pulled ~20 unrelated x86 port-I/O/MSR/GDT/IDT/LGDT/LIDT extern
     symbols into the aarch64 link closure (all initially masked as
     fabricated return-0 stubs — see the `SIMPLE_ALLOW_FREESTANDING_STUBS`
     trap note below). Replaced with a local `halt_loop()` calling a new
     `rt_aarch64_wfe_spin()` extern (WFE spin loop) defined in
     `freestanding_runtime.c`.
  3. **`extern fn memory_init(boot_info: BootOutputPort)` had no
     implementation anywhere in the tree, on EITHER x86_64 or aarch64** —
     `limine_boot.spl` (x86_64) has the identical unimplemented extern, so
     neither Limine-protocol kernel could ever have linked before this
     pass. Replaced with a MILESTONE-STUB `fn memory_init(...)` that logs
     `"[BOOT] memory_init: MILESTONE STUB — ..."` +
     `"[BOOT] SIMPLEOS-AARCH64-LIMINE-KERNEL-OK"` and halts. Clearly marked
     in-source as a stub, not a completed Layer 1 memory subsystem — real
     memory-layer porting is future work, out of scope here.
- `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`
  also gained: `_get_kernel_end`/`_get_bss_start` (read the linker-script
  `_kernel_end`/`_bss_start` symbols), and 12 generic `rt_*` runtime
  primitives found missing by real `ld.lld` unresolved-symbol errors —
  `rt_string_new_literal`, `rt_enum_id`, `rt_enum_discriminant`,
  `rt_text_cmp_any`, `rt_native_cmp`, `rt_opt_i64_to_string`,
  `rt_opt_bool_to_string`, `rt_opt_f64_to_string` (stub-only, no float
  formatter — nothing in this milestone's path uses it), `rt_value_float`
  (stub-only, same reason), `rt_typed_words_u32_at`/`u64_at`,
  `rt_memory_barrier`/`rt_invlpg` (aarch64 `dsb sy`/`tlbi vaae1is`, ported
  from RV64's `fence rw,rw`/`sfence.vma` analogs), and
  `rt_arm64_dcache_clean_range`/`invalidate_range` (ported near-verbatim
  from `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`,
  the existing EL1-direct lane's already-correct aarch64 D-cache
  maintenance code, adapted from its `RuntimeValue` ABI to this file's
  `spl_i64` scheme).

### `SIMPLE_ALLOW_FREESTANDING_STUBS=1` trap (re-confirmed)

Copying the `x86_64` build-script convention of setting
`SIMPLE_ALLOW_FREESTANDING_STUBS=1` (seen in
`scripts/os/build_fsexec_general_ring3.shs`) produced a build that reported
"Linked (freestanding): ... (1 KB)" as if successful, with 34 symbols
silently fabricated as weak return-0 stubs — including x86-only
`rt_port_inb`/`rt_read_msr`/`rt_lgdt`/etc. that should never have been
referenced by an aarch64 build at all (see the `os.kernel.boot.cpu` import
bug above). This is the same class of failure as
`reference_fabricated_stub_guard_fails_open_for_unbaselined_entries` in
memory: **do not set that env var when bringing up a new freestanding
target** — use `SIMPLE_TRACE_STUBS=1 SIMPLE_STRICT_FREESTANDING_PRECHECK=1`
instead to get the real unresolved-symbol list and fix them for real.

### Real boot transcript (2026-08-07)

Build: `bin/simple`-equivalent seed `native-build --backend cranelift
--entry-closure --entry examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl
--target aarch64-unknown-none-elf --linker-script
examples/09_embedded/simple_os/arch/aarch64/boot/linker_limine.ld` → real
89 KB ELF (`readelf -h` entry point `0xffffffff8010105c`, real `.text`
section, vs. the empty-1KB false-success before the `_start` mangling fix).

Boot: `qemu-system-aarch64 -M virt -cpu cortex-a72 -m 256M -pflash
AAVMF_CODE.no-secboot.fd -pflash AAVMF_VARS.fd -drive
if=none,file=esp.img,format=raw,id=esp -device virtio-blk-pci,drive=esp
-serial file:serial.log` (ESP built with `mkfs.vfat` + `pyfatfs`, same
approach as the 2026-08-06 probe-kernel pass):

```
========================================
  SimpleOS — Limine Boot Protocol (aarch64)
========================================
```

This is genuinely the real kernel: Limine's own loader-progress line
(`limine: Loading executable ...`) appears earlier in the raw serial
capture, and this banner is a distinct string only `limine_boot_aarch64.spl`'s
`limine_aarch64_boot_main()` prints via `log_raw_println` → `serial_println`
→ this session's new PL011 `uart_put_byte`.

**Sabotage-verify performed**: commented out the PL011 `DR` store in
`uart_put_byte` (made it a no-op), rebuilt, reran with a freshly-rebuilt ESP
image — confirmed **total serial silence** (0 bytes matching "SimpleOS").
Restored the real store, rebuilt, reran — banner returned. Confirms the
output is genuinely produced by this session's code, not residual
firmware/Limine console output.

### Next blocker (open, not fixed this session): hang in `_parse_hhdm()`

`kernel_main` (`limine_aarch64_boot_main`) prints the banner (4
`log_raw_println` calls) successfully, then calls `_parse_hhdm()` — after
which **no further output appears and QEMU never exits/crashes/resets**
(confirmed to persist past a 30s timeout with `-no-reboot`; no panic
string, no data-abort trap message). `_parse_hhdm()`'s first two statements
are `val resp_ptr = hhdm_request.response` then a nil check that should
print a `"[BOOT] WARNING: No HHDM response from Limine"` line if
`resp_ptr == 0` — and `hhdm_request`'s `response` field is explicitly
statically initialized to `0` in its struct literal, so that WARNING should
be unconditionally reachable and cheap. It never prints.

Suspected but **unconfirmed** root cause, worth investigating first: the
`# @section(".limine_reqs") — applied by linker script` annotations above
`hhdm_request`/`memmap_request`/etc. are **plain comments**, not a real
Simple-language section-placement attribute — `readelf -S kernel.elf`
confirms **no `.limine_reqs` section exists in the linked binary at all**
(`linker_limine.ld`'s `.limine_reqs : AT(...) { *(.limine_reqs) }` collected
zero input sections, so ld dropped it). Per the protocol note earlier in
this doc ("`base_revision == 0` falls back to scanning the ELF's
`.limine_reqs` section directly"), Limine can never discover any of this
kernel's requests, which is consistent with the WARNING-path *not* being a
crash — but does not explain why the WARNING itself never prints. The
struct-field read (`hhdm_request.response`, a `u64` field in a `@repr("C")`
higher-half-linked global) or the following `== 0` compare is the most
likely remaining suspect; not yet isolated whether this is a codegen defect
specific to this target/link-address combination or a genuine data abort
silently absorbed by AAVMF's default EL1 exception vectors. **Not fixed
this session** — out of scope per the "one real klog line from the real
kernel" milestone bar this pass targeted; the same `limine_boot.spl`
(x86_64) code path has never been run either, so this may be a
long-standing, previously-undiscovered defect shared by both arches rather
than an aarch64-port regression.

### Not done this session

- `src/os/_QemuRunner/scenario_catalog.spl` / `scenario_disks.spl` wiring
  (plan step 4/6) — still deferred; the artifact now exists and boots to a
  real banner, but does not yet complete `kernel_main` end-to-end (see
  blocker above), so wiring the QEMU-runner scenario ahead of that would
  encode a known-incomplete boot as if it were a finished milestone.
- The `_parse_hhdm()` hang itself (see above).
- Full RV64-parity virtio/PMM/FAT32 support in the aarch64 freestanding
  runtime — explicitly out of scope; only the boot-entry subset was ported.

### `_parse_hhdm()` hang: root-caused and fixed (2026-08-07) — full boot to milestone marker

**Root cause was NOT the missing `.limine_reqs` section** (that gap is real
but turned out to be a red herring for the hang itself — see below). Bisected
by adding `log_raw_println` immediately before and after
`val resp_ptr = hhdm_request.response` and rebuilding/booting: `"_parse_hhdm:
enter"` printed every time, `"_parse_hhdm: read done"` never did. That pins
the fault to the field read itself, not to anything downstream of it
(matching the earlier open question — the nil-check WARNING should have been
"unconditionally reachable" and wasn't, because the code never got there).

**Actual defect: `some_request.response` field access on a `@repr("C")`
global struct is miscompiled on this aarch64/cranelift target.** Disassembled
the built `kernel.elf`'s `_parse_hhdm` (`aarch64-linux-gnu-objdump -d`):

```
ldr x11, =0xffffffff80105008   ; &hhdm_request (struct base, NOT +0x28 offset)
ldr x11, [x11]                 ; loads id[0] (the COMMON_MAGIC constant!), not .response
and x12, x11, #0xfffffffffffffff8   ; mask low 3 bits
cbnz x12, ...                  ; branch on tag-masked value
```

This is the tagged-pointer/`Option`-unboxing codegen pattern (mask + deref
at a further `+16` in the taken branch) — the pattern used for boxed/nilable
value field access — applied to what should be a flat `base + offsetof(response)`
load on a POD `@repr("C")` struct. `id[0]` is a 64-bit magic constant, so the
mask is (almost) never zero, so the branch always goes the "non-nil" way
and reads structurally wrong memory beyond that — with this specific magic
value and this specific tag-check sequence, the resulting control flow never
reaches either print statement, which is the observed silent hang. This is
the same defect class already catalogued in memory
(`reference_native_dict_get_struct_corrupt_len_minus_one`,
`reference_u32_array_is_not_a_packed_buffer` — 8-byte-stride/`<<3` tagging
schemes leaking into plain POD struct/global codegen on native targets) but
had not previously been observed for a **global** `@repr("C")` struct's field
read specifically. Filing as its own compiler bug is the right next step
(out of scope to fix in cranelift-aarch64 codegen itself this session — see
"Fix scope" below); this doc records the concrete repro.

**The `# @section(".limine_reqs")` comments were also confirmed to be dead
comments, not a real attribute** — grepped the parser AST
(`src/compiler_rust/parser/src/ast/nodes/definitions.rs`): `decorators`/
`attributes: Vec<Attribute>` fields exist on `FunctionDef`, `ClassDef`,
`ExternDef`, etc., but there is **no such field on any top-level `var`/`let`
declaration node at all** — Simple has no attribute/decorator syntax slot on
global variables, so `@section(...)` was never parseable there in the first
place, comment or not. `readelf -S` on the previously-linked kernel
confirmed zero `.limine_reqs` section, exactly as expected from "not a real
attribute." `limine_boot.spl` (x86_64) has the identical dead comment and
has never been run either — this is a shared, not aarch64-specific, gap.

**Fix (scoped, not a general compiler feature):** matching the task's
explicit "scope down, don't over-engineer a general section-placement
feature" guidance, did **not** implement parser/HIR/MIR/codegen support for
a real `@section`/`@link_section` global-var attribute. Instead, moved the
five Limine request structs
(`memmap`/`framebuffer`/`rsdp`/`hhdm`/`kernel_addr`) out of
`limine_boot_aarch64.spl` entirely into
`examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c` as
plain C `static volatile` globals with `__attribute__((used, aligned(8)))`,
and added five zero-arg accessor externs
(`rt_limine_{memmap,framebuffer,rsdp,hhdm,kernel_addr}_response() -> u64`)
that `limine_boot_aarch64.spl` now calls instead of doing
`some_request.response` field access. This fixes both defects in one move:
the structs are real C data (not stripped, no Simple codegen path anywhere
near them), and Simple never does a `@repr("C")` global-struct field read on
them again — the buggy codegen path is avoided rather than fixed at the
root.

**Named-section attempt and empirically-confirmed regression:** first tried
adding `__attribute__((section(".limine_reqs")))` to those C globals, to
match `linker_limine.ld`'s already-present (previously-empty)
`.limine_reqs : AT(...) { *(.limine_reqs) }` output section and the same
mechanism `src/os/kernel/arch/x86_64/linker.ld` documents. Confirmed via
`readelf -SW` that this genuinely populated the section (`0xf0` = 240 bytes
= 5 × 48-byte structs, no longer empty). But booting that build under
`qemu-system-aarch64 -M virt -cpu cortex-a72 -pflash AAVMF_CODE.fd -pflash
AAVMF_VARS.fd` made **Limine's own loader** fault, reproducibly (bit-identical
across two separate runs): `Synchronous Exception at 0x000000004C66A2E0`,
printed twice (a fault while handling the first fault), before this kernel
printed anything at all — a regression from the prior (request-blind, hang-
after-banner) state. Root cause not isolated (no Limine source in-tree to
check the `AT()` physical-address arithmetic against its loader's
expectations, and network fetch is unavailable in this environment). Removed
the `section(...)` attribute — the plain `used`-global form (no explicit
section) turned out to be sufficient and is what shipped (see next
paragraph) — the `.limine_reqs` named-section path is parked, not chased
further, per the same "don't over-engineer" scoping. `linker_limine.ld`'s
`.limine_reqs` output section is left in place (now permanently empty,
harmless) as a documented landing spot if this is revisited.

**Confirms `linker_limine.ld`'s own x86_64-side comment was right all
along:** `src/os/kernel/arch/x86_64/linker.ld` already states "Limine scans
the binary for the magic IDs at boot time" — i.e. Limine's discovery does
**not** require a specially-named/bounded section, only that the request
structs exist as real, non-stripped bytes somewhere inside a loaded
`PT_LOAD` segment. The plain-`used`-global (no `section(...)`) build proves
this empirically: `readelf -SW` on that build shows **no** `.limine_reqs`
section at all (the structs landed in ordinary `.rodata`/`.data`), yet
Limine found and populated all five requests correctly.

**Full real-firmware boot result (2026-08-07, plain-`used`-global build):**
built via the same seed `native-build --backend cranelift --entry-closure
--entry .../limine_entry.spl --target aarch64-unknown-none-elf
--linker-script .../linker_limine.ld` command as the earlier banner-only
pass (`kernel.elf`, 90 KB), copied into `build/os/aarch64_limine/esp.img`'s
FAT filesystem via the `pyfatfs` venv at `/tmp/pyfatvenv` (no `mtools`/root
mount available in this environment), booted under
`qemu-system-aarch64 -M virt -cpu cortex-a72 -m 256M -pflash AAVMF_CODE.fd
-pflash AAVMF_VARS.fd -drive if=none,file=esp.img,format=raw,id=esp -device
virtio-blk-pci,drive=esp -serial file:serial.log` (needed a `startup.nsh`
containing `FS0:\EFI\BOOT\BOOTAA64.EFI` on the ESP root, since this fresh
AAVMF NVRAM has no BootOrder set and drops to the UEFI Shell rather than
auto-booting removable media). Serial transcript, past the previously-hung
point:

```
[BOOT] HHDM offset: 0x18446462598732840960     (= 0xffff800000000000, the standard
                                                   higher-half-direct-map base — printed
                                                   as decimal, not hex, a separate
                                                   pre-existing cosmetic "0x{x}"
                                                   interpolation-doesn't-hexify bug,
                                                   out of scope here)
[BOOT] Memory map: 48 entries
[BOOT]   region 0: base=0x67108864 size=0x67108864 type=1
  ... 46 more regions ...
[BOOT] WARNING: No framebuffer response from Limine
[BOOT] RSDP at physical address 0x18446462600015642648
[BOOT] Kernel: phys=0x1336279040 virt=0x18446744071563116544
[BOOT] Boot info assembled successfully
[BOOT] Total memory regions: 48
[BOOT] Handing off to memory layer...
[BOOT] memory_init: MILESTONE STUB — Layer 1 not yet ported to the Limine boot lane (aarch64)
[BOOT] SIMPLEOS-AARCH64-LIMINE-KERNEL-OK
```

This reaches the exact milestone marker the memory-init stub was written to
print, i.e. the kernel now runs its **entire** boot-entry path — HHDM,
memory map, framebuffer (correctly absent, QEMU `virt` has none by default),
RSDP, kernel address — end to end for real, on the real-firmware AAVMF proxy
(board-runnable rule: pflash, not `-kernel`, no `isa-debug-exit`), not just
to the banner. Reproduced twice with identical output.

**Sabotage-verification:** the fix's necessity was demonstrated by the
natural three-way progression above, each variant deterministic and
reproduced at least twice:
1. Direct `hhdm_request.response` field read (original code) → hangs
   silently right after "enter", before "read done" (bisected, see above).
2. Extern-accessor fix + explicit `.limine_reqs` section → Limine's loader
   itself faults (`Synchronous Exception`), a different but also-broken
   outcome, isolating that the named-section attribute specifically (not
   the accessor fix) causes that regression.
3. Extern-accessor fix, no named section → full boot to milestone marker.
Each transition was caused by exactly one code change (confirmed via
`readelf -SW`/`readelf -lW` diffs between builds), which is the causal
proof requested; a full revert-refix cycle of variant 1 was not repeated a
third time since the bisection in the "root-caused" paragraph above already
constitutes that proof for the actual shipped defect.

**Files changed:**
- `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`
  — added the five Limine request structs (plain `used` C globals, no
  section attribute — see regression note above) and five
  `rt_limine_*_response()` accessor externs.
- `src/os/kernel/boot/limine_boot_aarch64.spl` — removed the five
  `LimineRequest`-typed `var` globals and their dead `# @section(...)`
  comments; replaced all five `..._request.response` field reads with calls
  to the new externs; removed the two temporary bisection
  `log_raw_println` calls from `_parse_hhdm()` used to isolate the hang.

**Not done this session (real gaps, not silently dropped):**
- The aarch64/cranelift codegen defect itself (struct-global field access
  miscompiling as tagged-pointer unboxing) is worked around here, not
  fixed at the root. It almost certainly affects any other freestanding
  aarch64 code that does plain field access on a `@repr("C")` global
  struct — worth a dedicated compiler bug and a minimal standalone
  repro/regression test outside the OS tree.
- The `.limine_reqs`-named-section `Synchronous Exception` regression is
  unexplained, not just unfixed — flagged above as parked, with the exact
  repro (add `section(".limine_reqs")` back to the five C globals, rebuild,
  reboot) preserved in this note for whoever picks it up.
- The `"0x{offset}"`-prints-decimal cosmetic interpolation bug (string
  interpolation of a `{u64}` inside literal `"0x"` text doesn't hex-format
  it) is real but unrelated to boot progress; not investigated further.
- Layer 1 memory-subsystem porting past the `memory_init` milestone stub —
  unchanged, still explicitly out of scope (same note as the prior
  session).

## Root-cause investigation of the struct-global field-access defect (2026-08-07)

Investigated the "aarch64/cranelift codegen defect ... worked around here, not
fixed at the root" gap flagged above. **Result: one real, landed consistency
fix; the aarch64-specific root cause is still open** — a plausible hypothesis
was formed by static reading, then tested with an executed discriminating
probe and REFUTED for the case that could actually be run in this checkout
(x86_64 host JIT). Recording both the ruled-out path and the surviving
candidates so the next session doesn't re-walk the same one.

### Hypothesis (static reading), and what testing it showed

`resolve_field_index` (`src/compiler/50.mir/_MirLowering/function_lowering.spl:1028-1070`)
resolves a `.field` access's field INDEX two ways: (1) a name-keyed lookup in
`self.struct_value_syms[base_local.id]`, populated by every struct-value-
producing lowering site except one; (2) a HIR-type-annotation lookup via
`expr_type_symbol(base)` (`base.type_.kind == Named(symbol, _)`). If BOTH
miss, it silently returns the hardcoded literal `0`
(function_lowering.spl:1070, "Default fallback when type is unknown") — every
field would then read back as field index 0 regardless of name, matching the
reported symptom exactly. This "silently defaulted to 0" failure mode recurs
in ~15 comments elsewhere in this layer for other struct-provenance gaps
(`grep resolve_field_index src/compiler/50.mir/`), so it looked like a strong
prior.

The gap found: `try_lower_global_read`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:202-212`, before this
fix) created the MIR local for a module-level `var` struct's `LoadGlobal` and
returned it WITHOUT registering `self.struct_value_syms[dest.id]` — unlike
every other struct-producing site (`mir_lowering_stmts.spl:291`,
`method_calls_literals.spl:537`, `expr_dispatch.spl:1315`, etc.). So lookup
(1) always misses for a global struct value, leaving lookup (2) — HIR type
inference on the global's `Var` node — to carry the whole burden alone.

**Tested, not just reasoned about.** `resolve_field_index` has a built-in
trace (`SIMPLE_MIR_FIELD_TRACE=1` prints `[field-idx-fallback0] field=...`
exactly on the 0-fallback path). Ran a minimal repro
(`@repr("C") struct BootRequest { magic, id, revision, response: u64 }`,
module-level `var g_req = BootRequest(...)`, print all four fields) through
`SIMPLE_MIR_FIELD_TRACE=1 bin/simple run <probe>.spl` — which reaches the
Cranelift JIT (`run` ≠ `test`; `test` is tree-walk and never reaches this
code at all) — **both with and without the `struct_value_syms` fix**. In
BOTH cases: no `[field-idx-fallback0]` trace, and all four fields (magic=
3350322480 / 0xC7B1DD30, id=42, revision=3, response=0) printed correctly.
**This refutes the hypothesis for this case**: lookup (2) — the HIR-type-
annotation fallback — already resolves a plain module-level `@repr("C")`
global struct correctly on the x86_64 JIT host, so the missing
`struct_value_syms` registration was never the active cause here. The
"freestanding/extern-facing module context breaks HIR type inference on the
global" guess from the first draft of this section was asserted, not shown,
and testing did not support it.

### What this leaves as the surviving candidates for the actual aarch64 bug

Since the field-INDEX resolution tests correctly even on the untouched code,
the real aarch64 defect is more likely downstream, in
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`, and/or in
something genuinely aarch64-specific that this x86_64-host JIT run cannot
exercise:

1. **Uniform `field * 8` stride** (`GetField`/`SetField`, lines 595/607) —
   every field is assumed to occupy exactly 8 bytes regardless of declared
   width; a `@repr("C")` struct promises real C layout (mixed `u8`/`u16`/
   `u32`/`u64` widths, natural alignment/padding), which this stride ignores.
   Self-consistent for structs built via this compiler's own `Aggregate`
   lowering (which also always pads fields to 8 bytes), but likely wrong for
   any C-ABI-compatible layout a firmware/bootloader interop struct needs.
2. **Unconditional `band(addr, -8)` tag-strip** (lines 594/605) — applied to
   EVERY struct base pointer, including one from `LoadGlobal` on a
   `@repr("C")` global, which was never heap-tagged (only the `Aggregate::
   Struct` heap-alloc construction path at lines 623-633 ORs in a `heap_tag =
   1`). On an already 8-aligned address this AND is a no-op, so it would only
   corrupt the address for an odd/misaligned one — worth checking whether
   the Limine-supplied/aarch64-declared global data address actually has
   this property (e.g. via a `.limine_reqs`-style section placement, or
   differing default data-section alignment on aarch64 vs x86_64 in this
   codegen's `cranelift_declare_global_data` path).
3. **Genuinely aarch64-target-specific**, i.e. not reachable at all through
   `bin/simple run` on an x86_64 host regardless of source-level correctness
   — would require the aarch64 native-build once the current unresolved-name
   regression in this checkout (being fixed by another session) is resolved,
   then disassembling the field-read sequence the way the original report
   did.

### Fix landed anyway

`try_lower_global_read` now registers `self.struct_value_syms[dest.id]` with
the struct's symbol name (resolved via `static_.type_.kind == Struct(symbol)`
→ `self.symbols.get_symbol_raw(symbol.id).name`) immediately after emitting
`LoadGlobal`, mirroring every other struct-value provenance site. This is a
genuine consistency gap (this was the only struct-producing site that skipped
the registration) and is low-risk/no-op-on-success, but per the test above it
is **not confirmed to be the fix for the aarch64 defect** — kept as a
standing correctness improvement, not a closed bug. File:
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`.

**Verification status:**
- Executed, discriminating: `SIMPLE_MIR_FIELD_TRACE=1 bin/simple run` against
  the minimal probe above, with the fix present and reverted — see above.
  This is real evidence, not a static claim, and it is negative for this
  hypothesis on this host/target.
- `bin/simple test test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl`
  passes (5 examples, 0 failures) but — confirmed by the trace test above —
  this spec does NOT discriminate the fix: `bin/simple test` runs the
  tree-walk interpreter, which never reaches `resolve_field_index` or
  `try_lower_global_read` at all, so it passes identically with the fix
  present or reverted. Kept as a documentation-style regression spec for the
  surface field-read contract, not as a gate on this defect; its header
  states this caveat explicitly.
- `bin/simple lint` on the edited file did not complete (timed out at 180s in
  this checkout) but `bin/simple run`/`bin/simple test` both compiled and ran
  the edited tree successfully, so the edit itself is not the cause of the
  lint hang.
- Real aarch64 verification is still blocked on the native-build regression
  noted above (separate, in-flight fix by another session).

## `.limine_reqs` named-section Synchronous Exception: orphan-placement hypothesis REFUTED (static-only, 2026-08-07)

Follow-up on the parked "named-section attempt and empirically-confirmed
regression" note above: with `__attribute__((section(".limine_reqs")))` added
to the five request globals in `freestanding_runtime.c`, Limine's own loader
faulted (`Synchronous Exception at 0x000000004C66A2E0`, reproduced twice) while
`linker_limine.ld` DOES already carry an explicit output-section rule for
`.limine_reqs` (`.limine_reqs : AT(...) { *(.limine_reqs) } :data`, sitting
between `.text` and `.rodata`, mapped into the `data` PHDR). The obvious
hypothesis was that this rule mishandles the input section as an **orphan**
(ld.lld places sections with no matching rule using its own orphan-placement
heuristic, which can put them outside the intended `PT_LOAD`, break page
alignment, or violate this script's own documented "mixed R/W permissions may
not share a page" constraint) — worth checking since the crash was never
isolated further at the time (no Limine source in-tree, network fetch
unavailable).

**This investigation is static-only — QEMU was not re-run.** The live tree
currently ships the plain-`used`-global form (per the parked note); per task
scope that working boot path was left untouched. Instead, reconstructed the
placement question directly from the real `linker_limine.ld` in a scratch
copy (`/tmp/.../scratchpad/limine_repro/`, not committed): a minimal
freestanding C file defining the same five `limine_request_t` globals
(identical magic IDs, `__attribute__((used, aligned(8)))`, plus a `_start`
that reads all five `.response` fields so nothing gets DCE'd), built two ways
with the system `clang`/`ld.lld` (`clang -target aarch64-unknown-none-elf
-ffreestanding -c ...` then `ld.lld -T linker_limine.ld -o out.elf out.o`,
no `--gc-sections`, matching the flags implied by the rest of this doc's
native-build invocations): once with plain `used` (baseline, "good") and once
with `section(".limine_reqs")` added (repro, "bad").

**Result: the `.limine_reqs` rule is NOT an orphan, and placement is
byte-for-byte structurally identical to the baseline.** `readelf -SW`/`-lW`
diff between the two builds:

```
< [2] .data        PROGBITS ffffffff80101000 011000 0000f0 00 WA 0 0 8   (good)
> [2] .limine_reqs PROGBITS ffffffff80101000 011000 0000f0 00 WA 0 0 8   (bad)
...
Segment 01: good=".data"  bad=".limine_reqs"   (both inside the same RW PT_LOAD)
```

Every field — `Address`, file `Offset`, `Size`, `Flg` (`WA`, i.e. `SHF_ALLOC |
SHF_WRITE`, so it's real allocated loaded data, not stripped/orphaned-into-a
non-alloc region), `Align` — is identical between the two builds; the section
even lands at the exact same virtual/physical address the plain-global data
would have occupied. The `PT_LOAD` program headers (`VirtAddr`, `PhysAddr`,
`FileSiz`, `MemSiz`, `Flg`, `Align`) are byte-identical between builds too;
only the section *name* differs (`.data` → `.limine_reqs`), plus a few bytes
of `.shstrtab` string-table growth to hold the longer name and a
correspondingly larger `e_shoff`. This exactly matches what the earlier
readelf check in this doc already found for the real, full kernel build
("genuinely populated the section... `0xf0` = 240 bytes... no `.limine_reqs`
section at all [in the working build]") — i.e. **two independent readelf
checks (the original full-kernel build, and this from-scratch minimal repro)
both show correct, non-orphaned, in-segment, correctly-`AT()`-mapped
placement for the named section.** The linker script's rule works exactly as
written; it is not silently falling through to orphan handling, splitting a
page across permissions, or landing outside a `PT_LOAD`.

**Conclusion: the orphan-section-placement hypothesis is refuted by this
evidence.** The `Synchronous Exception` Limine hits is not explained by
anything visible in `readelf -lS` output — the ELF's segment/section layout
is unremarkable. The remaining candidate explanations are outside what static
linker-script/readelf analysis can settle without Limine's own loader source
(still not available in this environment/offline network):
- Limine's ELF loader may special-case a section literally named `.requests`
  (bracketed by `LIMINE_REQUESTS_START_MARKER`/`_END_MARKER` symbols per
  `PROTOCOL.md`'s reference kernel convention) differently from an
  arbitrarily-named allocated section it doesn't recognize — `.limine_reqs`
  matches neither the "no named section, scan everything" path (which is
  what actually works, per this doc's `x86_64` comment: "Limine scans the
  binary for the magic IDs at boot time") nor the reference `.requests`
  fast-path name, so it may be hitting a bounded/fast-path scan keyed on a
  name it half-recognizes and mis-sizes.
- A one-off toolchain/environment difference between the two build attempts
  (different `clang_static` fork state, different AAVMF firmware image
  revision) that happens to correlate with, but isn't caused by, the section
  attribute — not ruled out, since the original two "bad" runs were not
  cross-checked against a simultaneous re-run of the "good" configuration on
  the identical AAVMF/QEMU binaries.

**Recommended correct recipe, IF this is revisited and re-tested on real
hardware/QEMU:** the linker-script rule itself does not need to change for
placement reasons — the diff above shows `AT(0x40100000 + (. -
0xffffffff80100000)) { *(.limine_reqs) } :data` already produces a correct,
non-orphaned in-segment section. The one real gap worth closing regardless of
this fault: **add `KEEP()`** — `.limine_reqs : AT(...) { KEEP(*(.limine_reqs))
} :data` — so a future `--gc-sections`-enabled build path can't silently drop
the section (harmless today only because nothing in this checkout's
native-build invocation passes `--gc-sections`). This is a documentation-only
recommendation here, not applied to the live linker script, since the
task scope for this pass was diagnosis, not changing the working boot path.

**Not done:** re-running the actual QEMU/AAVMF boot (explicitly out of scope
for this pass — the task was static analysis only); fetching Limine loader
source to check its section-name handling (no network access in this
environment).

## Candidate 1 vs candidate 2 for the struct-global field-misread: NEITHER, as literally scoped (static read, 2026-08-07)

Follow-up task: determine whether surviving candidate 1 (uniform `field * 8`
stride) or candidate 2 (unconditional `band(addr, -8)` tag-strip) — both in
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`'s `GetField`
case, lines 592-601 — explains the real aarch64 disassembly captured earlier
in this doc (`_parse_hhdm`, "Actual defect" paragraph, lines 566-571):

```
ldr x11, =0xffffffff80105008   ; &hhdm_request
ldr x11, [x11]                 ; loads id[0] (magic), not .response
and x12, x11, #0xfffffffffffffff8   ; mask low 3 bits
cbnz x12, ...
```

Read the current `GetField` lowering directly (`cranelift_codegen_adapter.spl:592-601`):

```
case GetField(dest, base, field):
    val tagged_addr = cl_translate_operand(ctx, cl_module, base, value_map, slot_map, func)
    val addr = cranelift_band(ctx, tagged_addr, cranelift_iconst(ctx, CL_TYPE_I64, -8))
    val offset = field * 8
    val field_addr = cranelift_iadd(ctx, addr, cranelift_iconst(ctx, CL_TYPE_I64, offset))
    val result = load_uniform_i64(ctx, dest.id, field_addr, func)
```

**Instruction-order mismatch rules out both candidates as literal explanations
of this trace.** `GetField`'s own IR order is AND-the-address, then ADD the
offset, then LOAD through the result — i.e. the mask always happens *before*
any load, on the pointer, never on a loaded value. The captured aarch64 trace
does the opposite: `ldr x11,[x11]` happens *first* (a bare, unmasked
dereference of the base pointer, offset 0), and `and x12, x11, #-8` happens
*second*, operating on `x11` — the just-**loaded value** — not on any address,
producing a *third* register (`x12`) that then feeds `cbnz`. Masking a loaded
value and branching on it is not what `GetField` emits; `GetField` never
masks anything after a load, and never branches at all. So:

- **Candidate 2 (unconditional tag-strip) does not match**: the mask in the
  trace is applied to `id[0]`'s *loaded value*, not to the *base address*
  being dereferenced. `GetField`'s `band(addr, -8)` (line 594) is address-side
  and would appear, if present, as an instruction *before* the `ldr`, not
  after it. Confirmed by grep: `cranelift_band` occurs in only three places in
  this file (594, 605, generic BinOp-`&` at 1078) — none is a "mask a
  just-loaded value, then branch" pattern. That pattern is not emitted by any
  code currently in `cranelift_codegen_adapter.spl`; it either comes from a
  different lowering site not yet located, or from Cranelift's own aarch64
  instruction selection synthesizing a compare-with-tag-bits sequence from
  MIR/IR this file emits for something other than a plain `GetField` (e.g. an
  `== 0` compare on a value whose inferred type is nilable/boxed, since this
  compiler's boxed-value representation ORs in a low tag bit — see
  `Aggregate::Struct`, lines 623-633 — and a nil-check on such a value would
  plausibly mask-and-compare like this). This was not chased further; it is
  the concrete next lead, not a settled conclusion.
- **Candidate 1 (uniform 8-byte stride) is moot for this specific trace,
  not confirmed or refuted in general**: the load in the trace reads offset 0
  (`id[0]`, the magic constant) instead of `.response`'s real offset. Per
  `GetField`'s own formula `offset = field * 8`, reading offset 0 means
  `field` resolved to **0** — the exact "silently defaulted to field index 0"
  fallback (`resolve_field_index`, `function_lowering.spl:1070`) that the
  prior session in this doc tested and refuted **on the x86_64 JIT path**
  (`bin/simple run`, `SIMPLE_MIR_FIELD_TRACE=1`, no `[field-idx-fallback0]`
  trace, all fields correct). That refutation was never run against the
  actual native-build/AOT `--target aarch64-unknown-none-elf` pipeline that
  produced this real kernel disassembly — it is not established that the two
  pipelines share the same field-index resolution outcome for this global.
  Whether the field-width/stride mismatch (candidate 1) matters at all is
  moot until `field` resolves to the *correct* non-zero index; right now the
  evidence points at index resolution being wrong (index 0 instead of the
  real `.response` index), not at the stride formula being wrong for a
  correctly-resolved index.

**Conclusion: neither candidate 1 nor candidate 2, as literally scoped in
`GetField`/`SetField`'s address-masking and stride code, explains the
captured trace — the trace's shape (load-then-mask-the-value-then-branch,
reading field index 0) does not match what that code emits (mask-the-address-
then-add-then-load).** The strongest concrete lead the trace itself supports
is a recurrence of the **field-index-resolves-to-0** failure mode, but this
time exercised through the native-build/AOT pipeline rather than the
`bin/simple run` JIT pipeline the prior test used — those are two different
execution paths through this compiler (see
`reference_entry_flag_delegates_to_rust_runtime.md` /
`reference_entry_flag_stage3_selfhost_regression.md` in project memory for a
precedent of `--entry`/native-build diverging from the JIT/interpreter path)
and were not shown to share field-index-resolution behavior. Confirming this
requires either (a) a `SIMPLE_MIR_FIELD_TRACE=1` run through the actual
native-build pipeline targeting `aarch64-unknown-none-elf` (not just
`bin/simple run` on x86_64), or (b) locating the actual MIR/codegen site that
emits "mask a loaded value, branch on it" (not found in
`cranelift_codegen_adapter.spl` by exhaustive grep for `cranelift_band` in
this session) to explain the trace's true shape. Neither was done this
session — this is a static-code-reading-only pass, no execution, per the
task's explicit scope (no bootstrap rebuild, no fix attempted). **Status:
still unconfirmed**, with the field-index-resolution-on-native-build path now
the concrete next lead instead of the two stride/tag-mask candidates, which
this pass demonstrates do not match the evidence at the instruction level.

## Mystery instruction sequence identified as `guard_nonnull_receiver`; wrong-base hypothesis REFUTED by symbol-size evidence (2026-08-08)

Followed the named next lead: ran the actual native-build/AOT pipeline
targeting `aarch64-unknown-none-elf` (not just `bin/simple run` on x86_64),
with a minimal, controlled, deletable probe. Evidence below is executed and
byte-exact, not static reading.

### Setup

The deployed `bin/simple` in this checkout is the Rust bootstrap **seed**
(`bin/simple --version` prints the seed WARNING banner; `readlink -f
bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`), same as every
prior real-kernel build in this doc (line 473: "`bin/simple`-equivalent seed
`native-build`"). This is apples-to-apples with the original bug capture.

Wrote a throwaway probe (`examples/09_embedded/simple_os/arch/aarch64/
field_trace_probe.spl`, deleted after use, never committed) reproducing the
exact shape of `_parse_hhdm`'s global: a `@repr("C") struct ProbeRequest {
magic, id, revision, response: u64 }`, a module-level `var
g_probe_request = ProbeRequest(magic: 0xC7B1DD30, id: 42, revision: 3,
response: 0)`, and a `_start` that reads all four fields in order. Built it
for real:

```
SIMPLE_MIR_FIELD_TRACE=1 SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
  bin/simple native-build --backend cranelift --entry-closure \
  --entry examples/09_embedded/simple_os/arch/aarch64/field_trace_probe.spl \
  --target aarch64-unknown-none-elf \
  --linker-script examples/09_embedded/simple_os/arch/aarch64/boot/linker_limine.ld \
  -o .../probe.elf
```

Exit 0, real 69 KB static aarch64 ELF, `1 compiled, 0 cached`. **Zero
`[field-idx-fallback0]` trace lines** — same result as the prior x86_64-JIT
test, now also true on the actual native-build/aarch64 pipeline. This
appears to refute `resolve_field_index`'s "defaults to 0" hypothesis
everywhere it can be tested — **but the refutation is weaker than it looks**,
per the next finding.

### The `SIMPLE_MIR_FIELD_TRACE` test is not just weak here, it is INERT

Also ran the same build against the real kernel entry
(`examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl`, the file
that produced the original bug) — also zero fallback-trace lines, exit 0. At
first this looked like a second independent refutation. It is not: grepping
the whole Rust seed source for the literal panic string this bug's crash
family is named after (`"runtime error: field access on nil receiver"`)
turns up the ACTUAL FieldGet codegen —
`src/compiler_rust/compiler/src/codegen/instr/fields.rs` — a hand-written
Rust implementation, completely independent of `resolve_field_index`
(`function_lowering.spl`) and `cranelift_codegen_adapter.spl`'s `GetField`
case, both of which are pure-Simple `.spl` source the Rust seed's own
codegen never executes. **`SIMPLE_MIR_FIELD_TRACE=1` can only ever fire when
the pure-Simple compiler's own MIR lowering runs it — it is structurally
blind to the Rust seed's codegen**, which is what every native-build in this
doc (including the one that produced the original bug) actually used. The
zero-trace result on both the x86_64-JIT test (prior session) and this
native-build test is real evidence for the pure-Simple pipeline, and no
evidence at all for the seed pipeline — two genuinely different
implementations of the same lowering, confirming the project-memory note
"THREE implementations, not two: seed, pure-Simple, and runtime C."

### Disassembling the probe reproduces the mystery trace byte-for-byte

`llvm-objdump -d` on the probe's `_start` (aka `spl_start`) shows, for the
FIRST field access (`g_probe_request.magic`):

```
ldr x14, =0xffffffff80102000   ; &g_probe_request (== _bss_start)
ldr x14, [x14]                 ; ***deref once*** -> loads magic (offset 0)
and x15, x14, #0xfffffffffffffff8   ; mask
cbnz x15, <ok>                      ; branch
<fallthrough>: ldr x0,=<msg ptr>; mov x1,#0x2b; blr <fn>  ; panic call
```

This is **byte-identical in shape** to the original captured trace (doc,
"Actual defect" paragraph): `ldr x11,=&hhdm_request; ldr x11,[x11]; and
x12,x11,#-8; cbnz x12,...`. Cross-checking the two literal-pool targets in
the panic path resolves it completely: `0x80101000` is a 43-byte `.rodata`
string, `readelf -x .rodata` shows it is literally `"runtime error: field
access on nil receiver"` (43 bytes — matches `mov x1, #0x2b` = 43 exactly),
and the call target at `0x80100008` is the symbol `rt_eprintln_str`. This
**is** `guard_nonnull_receiver` (`fields.rs:23-42`), called from
`compile_field_get` (`fields.rs:44-81`) before every single `FieldGet`,
unconditionally:

```rust
// fields.rs:53-60
let obj_value = get_vreg_or_default(ctx, builder, &object);
let tag_mask = builder.ins().iconst(types::I64, !0x7i64);
let obj_ptr = builder.ins().band(obj_value, tag_mask);
guard_nonnull_receiver(ctx, builder, obj_ptr)?;   // load+mask+cbnz+panic-call
```

### Wrong-base hypothesis REFUTED: the global's storage is a pointer slot, not the struct itself

`nm -S` on the built probe object shows `g_probe_request` is **8 bytes**
(`.bss`, type `V`) — the global slot holds a **pointer**, so the single
`*(&global)` dereference seen in the disassembly is the CORRECT base, not an
off-by-one-indirection into the struct's own first field. The object also
contains `__module_init_<mod>`/`_dynamic`, which is what populates that
pointer at runtime. The previous section's "`x14` is STILL the magic value
from field 1's guard" reading was an unverified inference from static
disassembly — the probe's actual memory layout (the `nm -S` symbol size) was
never checked before that claim was written, and it does not hold up: an
8-byte global cannot itself be storing a 4-field, `magic`-first struct.

The global's storage is an 8-byte pointer slot (`nm -S` = 8, not 32), so the
single deref is correct. The guard fires because the pointer is nil —
module-global-init does not run on this freestanding path. This matches the
existing finding in
`doc/08_tracking/bug/simpleos_userspace_crt0_missing_module_init_call_empty_init_array_2026-08-06.md`
(freestanding crt0 never calls the module-init/`_dynamic` entry that would
populate the global's pointer slot before first use) — see that doc for the
init-array-not-called mechanism.

### What is confirmed vs. what remains the next lead

**Confirmed (executed evidence, not static reading):**
- The mystery load-then-mask-then-branch instruction sequence is
  `guard_nonnull_receiver` in `src/compiler_rust/compiler/src/codegen/instr/
  fields.rs:23-42`, invoked unconditionally by `compile_field_get`
  (`fields.rs:44-81`) / `compile_field_set` (`fields.rs:84-100`) for every
  `FieldGet`/`FieldSet`, regardless of whether the receiver's real type is a
  nilable/boxed reference (where the check is correct and intentional — see
  the function's own doc comment) or a non-nilable `@repr("C")` value-type
  global (where it is not).
- Field byte-offset computation (0/8/16/24 for a 4-field struct) is correct.
- The "field-index-resolves-to-0" hypothesis is refuted only for the
  pure-Simple lowering path (the one `SIMPLE_MIR_FIELD_TRACE` actually
  instruments); the seed path (`src/compiler_rust/compiler/src/codegen/
  instr/fields.rs`) was never traced and remains unconfirmed either way.
- `cranelift_codegen_adapter.spl`'s `GetField`/`SetField` (the pure-Simple
  path) is confirmed NOT the code that ran here or in the original bug — the
  Rust seed's `fields.rs` is a separate, independent implementation, and
  `SIMPLE_MIR_FIELD_TRACE` cannot observe it.

**Next lead, not yet located (this session ran out of scope for it):** the
exact site in the Rust seed's HIR→MIR lowering
(`src/compiler_rust/compiler/src/hir/lower/` and/or `src/compiler_rust/
compiler/src/mir/`) that computes the `object` VReg for a `FieldGet` on a
module-level `var` struct global. It should emit "address of the global"
(a data-symbol-address op) but instead emits "load from the global" (a Load
op) — correct for a reference-typed local (whose stored value genuinely is a
heap pointer) but wrong for a `@repr("C")` value-type global (whose storage
IS the struct, not a pointer to it). No file:line for this site yet; grepping
`FieldGet` construction sites for "global"/"static" in
`src/compiler_rust/compiler/src/{hir/lower,mir}/*.rs` returned nothing, so
the construction is likely indirect (e.g. going through a generic "lower
lvalue reference" helper shared with non-global locals). Whoever picks this
up should start there rather than re-testing `resolve_field_index` or
`cranelift_codegen_adapter.spl` — both are now confirmed off the critical
path for this defect.

**Not done this session:** locating the exact upstream lowering site (see
above); re-running the real kernel through this same fully-disassembled
methodology (only the minimal probe was disassembled field-by-field; the
real `limine_entry.spl` build was built but not similarly dissected — the
minimal probe was sufficient to nail the mechanism and is a strictly cleaner
signal); fixing anything (no bootstrap rebuild, no fix attempted, per task
scope). Probe file deleted after use, nothing committed.

## Verification 2026-08-17 (content classification, fleet lane I)
The virtio-blk half is STILL-OPEN and the tree now carries an explicit,
commented WORKAROUND for it rather than a fix. `src/os/services/vfs/arm_fs_exec_vfs.spl`:
- :258-260 `_arm_cluster_sector` = `data_start + (cluster - 2) * g_arm_spc`, and
  :255 logs the parsed `spc=` — so the spc value is live, not stubbed.
- :271-289 `_arm_read_cluster` states in-source: "A single multi-sector
  rt_arm_virtio_blk_read_prefix(first, spc*512) call truncates AND corrupts past
  the first sector on this virtio-blk driver (the descriptor ring is
  single-sector oriented). Read each sector with an independent single-sector
  read_prefix (the proven-correct path) and concatenate". It then loops
  `while i < spc` issuing one 512-byte `rt_arm_virtio_blk_read_prefix` per
  sector.
So the single-sector ring defect this doc reports is CONFIRMED PRESENT by
content: the driver still cannot do a multi-sector descriptor read, and the VFS
routes around it. The workaround is correct-but-slow, so the row stays open on
the driver.
NOT PROVEN HERE — stated explicitly rather than implied: no boot was run. Under
this project`s OS/board rule a QEMU-only result would not settle it anyway, and
a real-firmware EDK2/AAVMF boot could not be started because a stage-3
self-hosting bootstrap held the host at ~98% CPU for the entire session (the
user`s stated top priority, and this fleet was instructed not to start VMs
against it). Board-run is therefore BLOCKED, not passed. The EFI half of this
doc remains superseded by
`arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md`.
