# Bare-Metal Examples

Minimal "hello world" examples for all 6 architectures.

## Build All Examples

```bash
./build.sh
```

## Architecture Support

| Arch | Status | Binary | QEMU Command |
|------|--------|--------|--------------|
| x86 32 | ✅ Built | hello_x86.elf | `qemu-system-i386 -kernel hello_x86.elf -nographic` |
| x86 64 | ✅ Built | hello_x86_64.elf | `qemu-system-x86_64 -kernel hello_x86_64.elf -nographic` |
| ARM M | ⚠️ Need compiler | hello_arm.elf | `qemu-system-arm -M lm3s6965evb -kernel hello_arm.elf -nographic` |
| ARM64 | ⚠️ Need compiler | hello_arm64.elf | `qemu-system-aarch64 -M virt -kernel hello_arm64.elf -nographic` |
| RV32 | ⚠️ Need compiler | hello_riscv32.elf | `qemu-system-riscv32 -M virt -kernel hello_riscv32.elf -nographic` |
| RV64 | ⚠️ Need compiler | hello_riscv64.elf | `qemu-system-riscv64 -M virt -kernel hello_riscv64.elf -nographic` |

## Install Cross-Compilers

```bash
# All architectures
sudo apt install gcc-multilib gcc-arm-none-eabi gcc-aarch64-linux-gnu gcc-riscv64-unknown-elf

# Then build
./build.sh
```

## Run Tests

```bash
# Simple test framework
simple test test/baremetal/ --only-slow
```
