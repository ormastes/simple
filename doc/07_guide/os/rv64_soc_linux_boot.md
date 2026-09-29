# RV64 SoC Linux Boot — Assets, Addresses, and Remaining Steps

Boot assets for running OpenSBI (and eventually Linux) on the landed Simple
RV64 SoC (`src/lib/hardware/soc_rtl/`), on GHDL/simulation and — per the
board-runnable rule — the K26 board once Lane N's clock/bitstream lands.

## Boot chain and load addresses

Fixed by `bootrom_read64` in `src/lib/hardware/soc_rtl/bootrom.spl`
(reset vector 0x1000; sets `a1`, jumps via `t0`, never returns):

| Addr         | What                | Who puts it there / who jumps |
|--------------|---------------------|-------------------------------|
| `0x00001000` | bootrom             | RTL ROM; sets `a1=0x88000000`, jumps `t0=0x80000000` |
| `0x80000000` | OpenSBI `fw_jump.bin` | preloaded into RAM; OpenSBI jumps to `FW_JUMP_ADDR` |
| `0x80200000` | kernel `Image`      | preloaded; entered S-mode(*) with `a0=hartid`, `a1=dtb` |
| `0x88000000` | `soc_virt.dtb`      | preloaded; `a1` from bootrom, `FW_JUMP_FDT_ADDR` in OpenSBI |
| above kernel | `initramfs.cpio.gz` | optional; advertise via `/chosen` `linux,initrd-start/end` |

(*) S-mode entry requires the core's S-mode support — see Gaps.

## Files

- `examples/09_embedded/simple_os/arch/riscv64/soc_virt.dts` — device tree
  matching the RTL exactly: 1 hart rv64imac, `memory@80000000` (128 MiB —
  must equal `dram_size` passed to `soc_top_64_init`), `clint@2000000`,
  `plic@c000000` (`riscv,plic0`, `ndev=31`, two contexts — ctx0 M-mode/MEIP,
  ctx1 S-mode/SEIP, matching `plic.spl`'s S-mode landing), `uart@10000000`
  (`ns16550a`, byte regs `reg-shift=0`/`reg-io-width=1`, PLIC source 10).
- `scripts/os/build_rv64_linux_assets.shs` — builds into `build/os/rv64_soc/`:
  - default: `soc_virt.dtb` (dtc) + `initramfs.cpio.gz` (freestanding static
    `/init`, `-march=rv64imac -mabi=lp64`, prints `SIMPLE-RV64-INIT OK`) +
    honest `manifest.txt` (each artifact BUILT/MISSING).
  - `--opensbi`: clones pinned OpenSBI v1.4, builds `fw_jump.bin` with
    `PLATFORM_RISCV_ISA=rv64imac_zicsr_zifencei PLATFORM_RISCV_ABI=lp64`,
    `FW_JUMP_ADDR=0x80200000`, `FW_JUMP_FDT_ADDR=0x88000000`.
  - `--kernel`: clones pinned Linux v6.6 stable and builds the rv64 `Image`
    (slow; opt-in). Until run, the manifest lists `Image` as MISSING — no
    fake image is ever produced.

## Clock TODO (blocks final DTB)

`clock-frequency` (UART) and `timebase-frequency` (CLINT `mtime` ticks once
per core clock) are set to the **25 MHz candidate** and marked
`TODO(laneN-clock)` in the DTS. Lane N owns the real PL clock decision
(core closes timing only ≤ ~33 MHz per the WNS probe). When it lands:
update both values in `soc_virt.dts`, rerun the build script.

## ISA note — rv64imac has no F/D

Everything loaded onto this core must be built soft-float:
- OpenSBI: ISA/ABI flags above (already in the script).
- Kernel: build with `CONFIG_FPU=n` (defconfig enables FPU; flip it before
  `Image` is used on the RTL core — QEMU rv64gc masks this mistake).
- Userspace/init: `-march=rv64imac -mabi=lp64` (script does this; a default
  glibc lp64d binary traps on the first FP instruction).

## Gaps to a live Linux boot (fail-closed list)

1. **S-mode in the core** — OpenSBI enters the kernel in S-mode and Linux
   needs Sv39 paging. Lane M's S-mode work must land first; until then the
   chain is provable only through OpenSBI banner + `fw_jump` handoff on the
   RTL/GHDL core. (QEMU's oracle `virt` CPU model has full S-mode/Sv39 and is
   not gated by this — see Verification snapshot below.)
2. **PLIC S-mode context — RESOLVED.** `plic.spl` now implements both
   contexts (ctx0 = M-mode/MEIP irq 11, ctx1 = S-mode/SEIP irq 9, landed with
   S-mode delegation 3b36b68cd11) and `soc_virt.dts` carries
   `interrupts-extended = <&cpu0_intc 11 &cpu0_intc 9>` matching it exactly.
   Verified live: QEMU's Linux PLIC driver reports
   `mapped 31 interrupts with 1 handlers for 2 contexts` when booted with our
   DTB (see transcript below) — same context/handler shape as QEMU's own
   `virt` DTB control run. No RTL/DTS change was needed; the only defect was
   a **stale compiled `soc_virt.dtb`** in `build/os/rv64_soc/` left over from
   before the DTS was updated to 2 contexts (it still had a single
   `interrupts-extended = <0x01 0x0b>` pair). Rebuilt via
   `dtc -I dts -O dtb -o build/os/rv64_soc/soc_virt.dtb
   examples/09_embedded/simple_os/arch/riscv64/soc_virt.dts` — always rerun
   `dtc` after any `.dts` edit; the plain (no-flag) invocation of
   `build_rv64_linux_assets.shs` does this automatically.
3. **CLINT vs SBI timer** — with S-mode, Linux uses the SBI timer (OpenSBI
   drives `mtimecmp`); no RTL change expected, but unverified on the RTL core
   (QEMU oracle run shows `riscv_clocksource`/`SBI TIME extension detected`
   cleanly with our DTB).
4. **Kernel image — DONE.** `--kernel` built Linux v6.6 rv64 Image (see
   manifest below). `.config` deltas verified to have survived
   `olddefconfig` intact (`# CONFIG_FPU is not set`,
   `CONFIG_SERIAL_8250=y`/`_CONSOLE=y`, `CONFIG_BLK_DEV_INITRD=y` all present
   in the final `.config`, not reverted).
5. **Board** — same artifacts must load on K26 once Lane N's timing-closed
   bitstream exists; QEMU/GHDL-only is not completion (board-runnable rule).
   Not attempted this wave (no board access) — filed as open, not silently
   scoped out.

## Verification snapshot (2026-07-22, this wave)

### Kernel Image build
- Linux v6.6, `ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu-`, rv64 defconfig +
  deltas (`CONFIG_FPU=n`, 8250 console, initramfs baked in). Build completed
  clean (`Kernel: arch/riscv/boot/Image is ready`); resumed from a prior
  detached `make -j$(nproc) Image` that had been `Terminated` mid-build by a
  session boundary — verified `.config` deltas had NOT been reverted by
  `olddefconfig` before resuming, then re-ran `make Image` to completion (no
  reconfigure, so no risk of re-reverting).
- `.config` deltas: `build/os/rv64_soc/kernel_defconfig_deltas.txt`
  (savedefconfig output, includes `# CONFIG_FPU is not set`, `CONFIG_SOC_VIRT=y`,
  serial 8250 block, `CONFIG_BLK_DEV_INITRD=y` +
  `CONFIG_INITRAMFS_SOURCE=".../initramfs.cpio.gz"`, `CONFIG_CMDLINE="console=ttyS0,115200"`).

### Artifact manifest (sha256)
| Addr | File | Size | sha256 |
|---|---|---|---|
| `0x80000000` | `fw_jump.bin` | 270,768 B | `bc1d788d5ca36c27c969d44c31129d5af07088b4b38832b8bc085167abae7510` |
| `0x80200000` | `Image` | 22,026,752 B | `5b2bd14b635200efd021a510866b1a23848c4acc22d47d3190e785bd82e7c99f` |
| `0x88000000` | `soc_virt.dtb` | 1,503 B | `c7708c2dc6e611fb9589411e03e0f58f43b6442dc47acfd721eaa152371181f3` |
| (initrd) | `initramfs.cpio.gz` | 775 B | `2123c66f88947e7e8ed8a37e7139a0d02425f75cbf03a3296c06e98c745b9179` |

(`soc_virt.dtb` sha256 above is the *rebuilt* one — see Gap #2 fix.)

### QEMU oracle: control run (QEMU's own `virt` dtb)
`qemu-system-riscv64 -M virt -m 256M -smp 1 -nographic -no-reboot -bios fw_jump.bin -kernel Image -initrd initramfs.cpio.gz -append "console=ttyS0,115200 earlycon=sbi"`
(no `-dtb`; RAM raised to 256M from the 128M manifest default so `FW_JUMP_FDT_ADDR=0x88000000` sits inside RAM — at 128M, `0x88000000` is exactly the RAM's exclusive top edge and OpenSBI silently faults on the FDT before printing anything).
Result: **OpenSBI v1.4 banner → Linux 6.6 boots → `plic: mapped 95 interrupts with 1 handlers for 2 contexts` → `Run /init as init process`.** No panic.
Transcript: `build/os/rv64_soc/transcripts/qemu_control_dtb.log`.

### QEMU oracle: our `soc_virt.dtb`
Same command + `-dtb build/os/rv64_soc/soc_virt.dtb`.
Result: **same milestone** — `OpenSBI v1.4` banner (`Platform Name: simple-soc-rv64`) → Linux 6.6 boots → `plic: plic@c000000: mapped 31 interrupts with 1 handlers for 2 contexts` (31 vs control's 95 = our smaller `riscv,ndev=31` device set, expected) → `Run /init as init process`. No panic, no divergence from control beyond the expected smaller device/memory footprint.
Transcript: `build/os/rv64_soc/transcripts/qemu_ourdtb.log`.

### Known cosmetic gap (not a boot failure)
Neither run prints the initramfs's `SIMPLE-RV64-INIT OK` marker — both hit
`Warning: unable to open an initial console.` (`init/main.c:console_on_rootfs`,
because the hand-built initramfs cpio has no `/dev/console` node, so init's
fd 1 write silently no-ops). This reproduces identically with QEMU's own dtb,
so it is an initramfs-construction gap, not a DTS/kernel/PLIC issue — the
kernel-boots-to-init milestone is unaffected. Fix (unattempted, needs root/
`CAP_MKNOD` unavailable in this sandbox) would be adding a `/dev/console`
char-device (5,1) node to the `init.c` cpio in `build_rv64_linux_assets.shs`,
or hand-crafting the cpio `newc` header bytes without `mknod`.

### `/init` binary
Verified `ELF 64-bit UCB RISC-V, RVC, soft-float ABI, statically linked`.

## Sanity tests (≤ 10 min, no kernel build)

Two fast gates prove the Simple RISC-V 32/64 cores are Linux-capable without
building or booting a full kernel. Both run offline and finish in well under ten
minutes. Run them after any change to `src/lib/hardware/{rv32i_rtl,rv64gc_rtl,soc_rtl}`
or `examples/09_embedded/fpga_riscv/rtl`.

### RV64 — privileged-mode boot probe (interpreter)
```sh
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_EXECUTION_MODE=interpreter \
  bin/simple run test/01_unit/lib/hardware/soc_rtl/soc_top_64_probe.spl
```
Expected last line: **`SOC64 PROBE: ALL PASS`** (runs in ~2–4 min). Proves the
`soc_top_64` core executes the full privileged sequence a Linux boot needs:
bootrom ABI + zero-extension, M/S/U privilege transitions, `ecall` trap
delegation (`medeleg`), `sret`/`mret`, and Sv39 `satp` write/read-back + address
translation. Run under the **interpreter** — the JIT backend has a known
simulation-only 61-bit boxed-int defect that corrupts full-64-bit array state
(`doc/08_tracking/bug/seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`);
it does **not** affect the VHDL→FPGA path (that backend never uses `RuntimeValue`).

### RV32 — FPGA load-path integrity gate (GHDL)
```sh
sh scripts/fpga/check_linux_loading_rv32.shs
```
Expected last line: **`CHECK_LINUX_LOADING_RV32: PASS`** (~15 s). Carries a
full-capacity 64 KB payload through the *real* BRAM `.mem` load path the
bitstream uses on hardware and checks that a checksum computed **by the core**
over the loaded region equals the host checksum (e.g. `883FEE27 == 883FEE27`).
RV32 has no MMU, so "load a Linux Image" is scoped honestly to load-path
integrity, not a boot (64 KB BRAM cap — see the results doc for the DRAM
blocker). Needs `ghdl` + `riscv64-unknown-elf-gcc`.

### Combined generated-RTL smoke
```sh
sh scripts/check/check-riscv-rtl-linux-smoke.shs [--rv32-only|--rv64-only]
```
Wraps the generated rv32/rv64 RTL Linux-handoff lanes. Note: the generated
handoff lane is more fragile than the two gates above (it re-runs the
`fpga_linux` bundle generator); prefer the two direct gates as the day-to-day
sanity anchors.

### Live re-verification (2026-07-23)
Rebuilt all assets from scratch (`build_rv64_linux_assets.shs --all`: OpenSBI
v1.4 `fw_jump.bin`, Linux **6.6.0** `Image` 22,026,752 B, `soc_virt.dtb`,
`initramfs.cpio.gz`) and booted under QEMU 8.2.2:

- **Full boot to userspace (auto-dtb + `rdinit=/init`):** `OpenSBI v1.4` →
  `Linux version 6.6.0` → `Freeing unused kernel image (initmem) memory` →
  `Run /init as init process` → **`SIMPLE-RV64-INIT OK`** (our initramfs `/init`
  marker, printed live — supersedes the "marker never prints" cosmetic gap noted
  below; `rdinit=/init` reaches it).
  Transcript: `build/os/rv64_soc/transcripts/qemu_control_live.log`.
- **Our `soc_virt.dtb` (`-dtb`) — now reaches userspace (initrd wiring fixed
  2026-07-23):** `OpenSBI v1.4` → `Platform Name: simple-soc-rv64` → `Linux
  version 6.6.0` → `Unpacking initramfs...` → **`Run /init as init process`**,
  **no VFS panic**. Fixed by adding `/chosen linux,initrd-start=0x88200000` /
  `linux,initrd-end=0x8820033d` (the address QEMU computes for the pinned
  initramfs — read it with `qemu-system-riscv64 -M virt,dumpdtb=…`) and raising
  the `memory@80000000` node to **256 MiB** in `soc_virt.dts`. A static `-dtb`
  cannot be auto-patched by QEMU, so the initrd address must live in the DTB; and
  the FDT at `0x88000000` (bootrom-fixed) plus the initrd above it need RAM past
  the 128 MiB edge. Boot command: the QEMU-oracle line above **plus** `-dtb
  build/os/rv64_soc/soc_virt.dtb` and `-m 256M`.
  Transcript: `build/os/rv64_soc/transcripts/qemu_ourdtb_wired.log`.
  Remaining cosmetic gap: our `/init`'s `SIMPLE-RV64-INIT OK` marker does not
  print under `-dtb` (it does under QEMU's auto-dtb) — kernel printk uses the SBI
  earlycon, but our `uart@10000000` node isn't bound as the `ttyS0` that init's
  fd1/`/dev/console` opens. A console-node/driver-binding detail, not the initrd
  wiring (the initramfs is unpacked and `/init` runs).

### Full Linux boot (heavier, needs a kernel build)
The real OpenSBI v1.4 → Linux 6.6 → `/init` boot (documented in the QEMU-oracle
sections above, `Platform Name: simple-soc-rv64`) requires the boot assets, which
are **not** checked in (`build/` is per-environment):
```sh
sh scripts/os/build_rv64_linux_assets.shs --all   # dtb+initramfs+opensbi+kernel (kernel build is slow, >10 min, needs net)
```
Then run the QEMU-oracle command in the section above. This exceeds the 10-minute
sanity budget because of the from-source kernel build; the two gates above are the
fast anchors.

### Note on the working tree
These gates compile the RISC-V hardware `.spl`/RTL directly, so a working copy
with leaked jj conflict markers or half-finished edits will fail them at
parse/analyse time (not a real regression). If a gate fails with `TripleLt`,
`AluResult32 not found`, or VHDL `missing entity/architecture`, first restore the
affected tree to the landed state:
```sh
git checkout origin/main -- src/lib/hardware/ examples/09_embedded/fpga_riscv/
```
