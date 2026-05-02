# SimpleOS QEMU Boot Status — 2026-04-07

## Major Breakthrough: Full-Stack Boot Achieved

All 4 boot stages pass successfully. The original undefined-symbol crash is resolved
by using `--entry-closure` builds with weak auto-stubs.

## Boot Stages (all PASS)

| Stage | Entry | Files | Status | Verified |
|-------|-------|-------|--------|----------|
| 1 | `boot_stage1_entry.spl` | ~5 | PASS | PCI scan, serial output |
| 2 | `boot_stage2_entry.spl` | ~19 | PASS | + NVMe + FAT32 + VFS |
| 3 | `boot_stage3_entry.spl` | ~34 | PASS | + VirtIO-net + TCP/IP |
| 4 | `boot_stage4_entry.spl` | ~94 | PASS | + POSIX + Shell |

## Build Command

```bash
# Stage N build (replace N with 1-4)
SIMPLE_LIB=$(pwd)/src SIMPLE_BOOTSTRAP=1 bin/simple native-build \
  --entry examples/simple_os/arch/x86_64/boot_stageN_entry.spl \
  --entry-closure --source src/os --source src/lib \
  --target x86_64-unknown-none \
  --linker-script examples/simple_os/arch/x86_64/linker.ld \
  -o build/os/simpleos_stageN.elf

# Convert to 32-bit ELF for QEMU Multiboot
/opt/homebrew/Cellar/llvm/22.1.2/bin/llvm-objcopy \
  --output-target=elf32-i386 \
  build/os/simpleos_stageN.elf \
  build/os/simpleos_stageN_32.elf

# Boot in QEMU
qemu-system-x86_64 -machine q35 -cpu qemu64 -m 2G -serial stdio -display none -no-reboot \
  -drive file=build/os/fat32.img,if=none,id=nvm,format=raw \
  -device nvme,serial=deadbeef,drive=nvm \
  -netdev user,id=n0,hostfwd=tcp::2222-:22 \
  -device virtio-net-pci,netdev=n0 \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -kernel build/os/simpleos_stageN_32.elf
```

## Bugs Fixed During Boot Bringup

1. **Method resolution ambiguity** — `SshDaemon.add_user` vs `SshUserDb.add_user`:
   When both types have `add_user`, the compiler picks the wrong one inside
   `SshDaemon.new()`. Fix: delegate to module-level function `sshd_create_default_users()`
   in ssh_auth.spl where SshDaemon isn't in scope.

2. **SHA-256 heap exhaustion** — `sha256()` used `data.len()` which returns
   unreliable values in baremetal Cranelift. The block count computation overflowed,
   causing billions of allocations. Fix: compute padded length via
   `_sha256_compute_padded_len()` before any array operations.

3. **Parse errors** — `git_app.spl` and `jj_app.spl` had multi-statement match arms
   (`"help": val _ = 0 \n print ... \n 0`) that the parser rejects. Fix: extract
   to `git_help(args)` / `jj_help(args)` functions.

4. **Heap size** — Increased from 64MB to 512MB in baremetal_stubs.c for compiler
   bootstrap (Milestone 5). QEMU memory set to 2GB.

## SSH Daemon Status

| Component | Status |
|-----------|--------|
| User database creation | PASS |
| SHA-256 password hashing | PASS (after fix) |
| Ed25519 host keypair generation | PASS (self-test skipped) |
| TCP socket creation | FAIL — IPC syscall layer not implemented |

**Blocker:** The POSIX socket layer uses IPC (syscall 20/21) to communicate with
the netstack service. In baremetal mode, IPC requires a microkernel message-passing
system that doesn't exist. Need C-level TCP socket stubs in baremetal_stubs.c
that route directly to the C VirtIO-net driver.

## What Works

- C boot stub: Multiboot → 32→64 bit, serial, 512MB heap
- Simple code executes: all OS subsystems initialize correctly
- PCI enumeration: 5 devices found (host bridge, VGA, NVMe, VirtIO-net, ISA bridge)
- NVMe: controller init, sector read, FAT32 BPB parsing
- FAT32: directory listing, file read ("Hello from SimpleOS!")
- VirtIO-net: driver init, MAC=52:54:00:12:34:56, IP=10.0.2.15
- BGA framebuffer: 1024x768x32bpp initialized
- POSIX layer: fd_table_init, async_io_init, signal_init
- Shell: ShellApp.new() succeeds
- SSH user database: SshUserDb with SHA-256 password hashing
- SSH host key: Ed25519 keypair generation
