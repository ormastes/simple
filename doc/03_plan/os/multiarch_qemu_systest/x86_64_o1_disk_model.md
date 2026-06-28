# x86_64 fs-exec Lane — O1 Disk Model Decision

**Status:** RESOLVED — recommendation (a) `-initrd`
**Author role:** helper agent (disk model + image audit only)
**Kernel agent scope:** `arch/x86_64/**`, `qemu_systest_contract.spl`,
`_SimpleosMultiplatformBuild/platform_target_catalog.spl` — do NOT touch those files.

---

## Decision: Option (a) — `-initrd build/os/fat32-x86_64.img`

### Rationale

x86_64 boots via **Multiboot1**. `crt0.s` declares a standard Multiboot1 header
(`MB_MAGIC = 0x1BADB002`, `MB_FLAGS = 0x3`) and saves the MBI pointer
(EBX → ESI → RBX → rdi into `spl_start`). QEMU supplies `-initrd` as a Multiboot
**module** (mods_count/mods_addr at MBI offsets [5]/[6]) — machine-independent and
fully supported on `-machine q35`.

x86_32 uses the identical mechanism (`-machine pc`, `-initrd`, Multiboot1,
`x86_32_capture_multiboot_modules` in baremetal_stubs.c) and **passes today**.
x86_64 is that same mechanism on a 64-bit crt0 — the lowest-risk, proven path.

Why not (b) `-drive + virtio-blk-pci`:
- riscv/arm use virtio-**mmio** on the `virt` machine. q35 would need **virtio-blk-pci**,
  which is unimplemented in `arch/x86_64/boot/baremetal_stubs.c`.
- Building a FAT32 PCI virtio stack is weeks of new work versus a one-function port.

Why not (c) embedded payload:
- Contradicts the "fs_exec" premise — the markers must assert real filesystem access
  and load, not a baked-in binary.

### Honesty scope of the markers

Under option (a), the honest assertion bar mirrors x86_32:
- `ELF_LOAD_OK` — Multiboot module arrived; FAT32 image detected; SMF/ELF blobs
  located by ASCII scan.
- `SMF_CLI_LAUNCH_OK` — synthetic syscall-ABI dispatch returns pid 2001 (hello).
- `SMF_WM_GUI_LAUNCH_OK` — synthetic syscall-ABI dispatch returns pid 2002 (browser).
- `NATIVE_GUI_PROCESS_RENDER_OK` — both synthetic pids > 0.
- `TEST PASSED` — all checks above passed.

This is **load-proof + dispatch-proof**, NOT real process execution. Same documented
bar as riscv64/x86_32.

---

## Recommended Contract Edit (for kernel agent, Opus coordinate)

In `src/os/qemu_systest_contract.spl`, replace `x86_64_qemu_args()`:

```
pub fn x86_64_qemu_args() -> [text]:
    ["-machine", "q35",
     "-cpu", "qemu64",
     "-m", "512M",
     "-nographic",
     "-initrd", "build/os/fat32-x86_64.img",
     "-device", "isa-debug-exit,iobase=0xf4,iosize=0x04",
     "-kernel", "build/os/simpleos_x86_64_fs_exec.elf"]
```

Notes:
- Keep `-machine q35`: crt0.s has explicit q35/OVMF-aware high MMIO mapping
  (comment at line 69, 122). Using `-machine pc` would lose those guards.
- `-device isa-debug-exit,iobase=0xf4,iosize=0x04` mirrors x86_32 and gives
  a deterministic `ioport(0xf4, 0)` exit on success, `ioport(0xf4, 1)` on failure.
  The entry can also rely on serial + timeout if the device is omitted.
- `x86_64_image_path()` already returns `"build/os/fat32-x86_64.img"` in the contract
  — no change needed there.

---

## Image Audit: `build/os/fat32-x86_64.img`

**Image exists:** YES — 4,194,304 bytes (4 MB)

**FAT32 BPB:** BPS=512, SPC=8, RSVD=32, FATs=1, FAT_SZ=64, RootClus=2.
FSType field is zero-filled (make_os_disk.c does not write the FSType string at offset
82) — this is cosmetic; the BPB is otherwise valid FAT32.

**Root directory structure:**
```
EFI/                (dir)
  BOOT/             (dir)
    BOOTX64.EFI     33 B
SYS/                (dir)
  APPS/             (dir)
    HELLOSMF.SMF    274 B   ← present, x86_64 ELF (e_machine=0x3e)
    BROWSMF.SMF     272 B   ← present, x86_64 ELF (e_machine=0x3e)
    SCOMPSMF.SMF    284 B
    SINTSMF.SMF     287 B
    SLOADSMF.SMF    282 B
    LLVMSMF.SMF     273 B
    CLANGSMF.SMF    274 B
    RUSTSMF.SMF     273 B
    STEAM204.SMF    351 B
  PERF/             (dir)
    CFAT4K.TXT       88 B
    FAT4K.BIN      8192 B
  NVFSVER.TXT        63 B
  TOOLSET.SDN        84 B
  MARKERS.TXT      1881 B   ← contains "HELLOSMF", "BROWSMF",
                                "SIMPLEOS_X86_64_HELLO_ELF",
                                "elf-machine=x86_64", lane info
  LLVMMAN.TXT, CLANGMAN.TXT, RUSTMAN.TXT, ...
KERNEL.ELF           29 B   (stub — no real kernel needed in image)
LIMINE.CNF          159 B
HELLO.TXT            20 B
NUMBERS.TXT           2 B
HELLO.SPL            41 B
```

**Required payloads for markers: ALL PRESENT.**
- `SYS/APPS/HELLOSMF.SMF` (274 B) — 64-bit ELF wrapping `SIMPLEOS_X86_64_HELLO_ELF`
- `SYS/APPS/BROWSMF.SMF` (272 B) — 64-bit ELF wrapping `SIMPLEOS_X86_64_GUI_ELF`
- `SYS/MARKERS.TXT` — contains `HELLOSMF`, `BROWSMF`, `SIMPLEOS_X86_64_HELLO_ELF`,
  `elf-machine=x86_64`

**No regeneration required.** The image was built with `platform=x86_64` by
`make_os_disk.c` and contains the correct x86_64-marker ELF stubs.

mtools was not available for verification; the above was confirmed via direct Python
FAT32 BPB/directory/content parsing.

**Regen command (if ever needed):**
```bash
# Compile make_os_disk.c first:
gcc -O2 -o build/os/make_os_disk scripts/os/make_os_disk.c
# Rebuild image (SIZE_BITS=64 for x86_64, KERNEL=any existing elf or /dev/null):
build/os/make_os_disk build/os/fat32-x86_64.img x86_64 64 build/os/simpleos_x86_64_fs_exec.elf
```
Kernel arg is read_file-optional (returns empty bytes on missing path), so any path works.

---

## Handoff Dependencies for Kernel Agent

The contract edit is necessary but NOT sufficient. The kernel agent must:

1. **Port `capture_multiboot_modules` to x86_64 in `arch/x86_64/boot/baremetal_stubs.c`:**
   x86_32's `x86_32_capture_multiboot_modules` (lines 704-762 in x86_32 stubs) reads
   `mbi[5]` (mods_count) and `mbi[6]` (mods_addr) and stashes `mod[0]/mod[1]` as
   initrd start/end. Port this as `rt_x86_64_initrd_present()`,
   `rt_x86_64_initrd_contains_hello_smf()` (scan for `"HELLOSMF"`),
   `rt_x86_64_initrd_contains_browser_smf()` (scan for `"BROWSMF"`),
   `rt_x86_64_initrd_contains_x86_64_marker()` (scan for `"SIMPLEOS_X86_64_HELLO_ELF"`
   or `"elf-machine=x86_64"`). Pointer type is `uint64_t` in the 64-bit stubs.

2. **Author `arch/x86_64/fs_exec_entry.spl`** mirroring
   `arch/x86_32/initrd_fs_exec_probe_entry.spl`. Wire to `rt_x86_64_initrd_*` externs.
   Emit `ELF_LOAD_OK` / `SMF_CLI_LAUNCH_OK` / `SMF_WM_GUI_LAUNCH_OK` /
   `NATIVE_GUI_PROCESS_RENDER_OK` / `TEST PASSED` on the live probe path.
   Each marker must assert a genuine probe result — do NOT print unconditionally.

3. **O2 — build target** in `_SimpleosMultiplatformBuild/platform_target_catalog.spl`:
   add `qemu_acceptance_lane` for x86_64 producing
   `build/os/simpleos_x86_64_fs_exec.elf`.

4. **`_start` MBI handoff**: crt0.s already zero-extends ESI into rdi before calling
   `spl_start`. The x86_64 stubs `_start(uint64_t mbi_ptr)` will receive it correctly —
   confirm the signature in `baremetal_stubs.c:_start`.

---

## Summary

| Item | Value |
|------|-------|
| O1 decision | **(a) `-initrd build/os/fat32-x86_64.img`** |
| Machine | `-machine q35` (keep — crt0 is q35-aware) |
| Boot protocol | Multiboot1 (existing crt0.s, unchanged) |
| Image present? | YES, 4 MB |
| HELLOSMF.SMF present? | YES, 274 B, x86_64 ELF |
| BROWSMF.SMF present? | YES, 272 B, x86_64 ELF |
| x86_64 marker in MARKERS.TXT? | YES (`SIMPLEOS_X86_64_HELLO_ELF`, `elf-machine=x86_64`) |
| Regen needed? | NO |
| Blocking kernel-agent items | stubs port + entry.spl + O2 build target |
