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
