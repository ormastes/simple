# SimpleOS QEMU Boot Status — 2026-04-04

## Build Status

| Target | Entry | Output | Size | Status |
|--------|-------|--------|------|--------|
| x86_64-unknown-none | `examples/simple_os/arch/x86_64/os_entry.spl` | `build/os/simpleos_fullstack.elf` | 270MB | Builds, links with stubs |
| x86_64 (32-bit wrap) | Same + `llvm-objcopy --output-target=elf32-i386` | `build/os/simpleos_fullstack_32.elf` | 270MB | Boots in QEMU |

## Build Command

```bash
# Build (45s)
SIMPLE_LIB=$(pwd)/src SIMPLE_BOOTSTRAP=1 bin/simple native-build \
  --entry examples/simple_os/arch/x86_64/os_entry.spl \
  --source src/os --source src/lib --source src/app \
  --target x86_64-unknown-none \
  --linker-script examples/simple_os/arch/x86_64/linker.ld \
  -o build/os/simpleos_fullstack.elf

# Convert to 32-bit ELF for QEMU Multiboot
/opt/homebrew/Cellar/llvm/22.1.2/bin/llvm-objcopy \
  --output-target=elf32-i386 \
  build/os/simpleos_fullstack.elf \
  build/os/simpleos_fullstack_32.elf

# Create FAT32 disk image
sh scripts/make_os_disk.shs 64 build/os/fat32.img

# Boot (QEMU 10.2.2)
qemu-system-x86_64 -machine q35 -cpu qemu64 -m 512M -serial stdio -display none -no-reboot \
  -drive file=build/os/fat32.img,if=none,id=nvm,format=raw \
  -device nvme,serial=deadbeef,drive=nvm \
  -netdev user,id=n0,hostfwd=tcp::2222-:22 \
  -device virtio-net-pci,netdev=n0 \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -kernel build/os/simpleos_fullstack_32.elf
```

## Boot Output

```
SimpleOS x86_64 boot
[BOOT] COM1 serial initialized at 115200 baud
[BOOT] Heap: 200 MB bump allocator
[BOOT] RuntimeValue: tagged 64-bit (int/heap/float/special)
[BOOT] Calling spl_start()...
FAULT @ 0x0000000000000003
```

## Root Cause: Undefined Runtime Symbols

| Metric | Count |
|--------|-------|
| **Defined rt_* symbols** | 383 (from `baremetal_stubs.c`) |
| **Undefined rt_* symbols** | 1,907 (resolved to address 0x0 by linker) |
| **Total rt_* needed** | 2,290 |
| **Parse errors (non-critical)** | 10 files |

The linker silently resolves undefined symbols to 0x0. When `spl_start()` calls a module-init function that references an undefined `rt_*` symbol, the indirect call goes to 0x0, causing a page fault. The exception handler converts this to nil (tagged 0x3), hence `FAULT @ 0x3`.

## What Works

- C boot stub: Multiboot → 32→64 bit mode switch → serial init → heap init
- Serial output via COM1
- QEMU device attachment (NVMe, VirtIO-net visible on PCI bus)
- Build system: Cranelift cross-compilation to x86_64-unknown-none

## What's Blocked

- `spl_start()` crashes immediately due to 1,907 undefined symbols
- No Simple code executes (os_main, posix_init, init_all_services, etc.)
- NVMe/VirtIO-net/FAT32/shell/SSH never reached

## Fix Options

1. **Extend baremetal_stubs.c** — add ~1,907 more return-nil stubs. Quick but masks bugs silently.
2. **Entry-closure build** — use `--entry-closure` to compile ONLY reachable code from os_main, reducing undefined symbols. Most of the 1,907 come from `src/app/` modules not needed by the OS.
3. **Minimal os_main** — create a stripped-down entry that avoids modules with many rt_* dependencies.

## Undefined Symbols List

Full list: `doc/08_tracking/bug/os_undefined_rt_symbols.txt` (1,907 entries)

## Interpreter Test Status

All OS integration tests pass in interpreter mode (23,167 tests, 0 failures):
- `test/system/os_storage_spec.spl` — NVMe + FAT32 + VFS
- `test/system/os_network_spec.spl` — VirtIO-net + TCP/IP  
- `test/system/os_shell_spec.spl` — Shell + VFS
- `test/system/os_ssh_spec.spl` — SSH daemon
- `test/system/os_full_stack_spec.spl` — End-to-end
