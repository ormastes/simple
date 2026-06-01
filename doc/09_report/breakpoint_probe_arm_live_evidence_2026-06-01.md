# Breakpoint Probe ARM-Family Live Evidence - 2026-06-01

Scope: bare-metal software-breakpoint probe images for ARM32, Thumb, and
AArch64 on QEMU `virt`.

Build commands used host Clang cross targets:

```bash
clang --target=arm-none-eabi -mcpu=cortex-a15 -marm ...
clang --target=arm-none-eabi -mcpu=cortex-a15 -mthumb ...
clang --target=aarch64-none-elf ...
```

QEMU commands:

```bash
qemu-system-arm -M virt -cpu cortex-a15 -nographic -monitor none -no-reboot -serial stdio -kernel build/baremetal/breakpoint_probe/arm32/breakpoint_probe.elf
qemu-system-arm -M virt -cpu cortex-a15 -nographic -monitor none -no-reboot -serial stdio -kernel build/baremetal/breakpoint_probe/thumb/breakpoint_probe.elf
qemu-system-aarch64 -M virt -cpu cortex-a57 -nographic -monitor none -no-reboot -serial stdio -kernel build/baremetal/breakpoint_probe/aarch64/breakpoint_probe.elf
```

Serial evidence:

```text
simple-breakpoint-evidence;arch=arm32;qemu=qemu-system-arm;address=1048576;original=00 00 a0 e1;trap=70 00 20 e1;hits=1;latency_us=1;restored=true;rearmed=true;cleanup=true;icache=true;sampled=none
simple-breakpoint-evidence;arch=thumb;qemu=qemu-system-arm;address=1048576;original=00 bf;trap=00 be;hits=1;latency_us=1;restored=true;rearmed=true;cleanup=true;icache=true;sampled=none
simple-breakpoint-evidence;arch=aarch64;qemu=qemu-system-aarch64;address=1048576;original=1f 20 03 d5;trap=00 00 20 d4;hits=1;latency_us=1;restored=true;rearmed=true;cleanup=true;icache=true;sampled=none
```

Notes:

- Thumb needs an ARM-state `_start` shim because QEMU enters the ELF in ARM
  state on the `virt` machine. The shim loads the Thumb-marked `probe_main`
  address and branches with `bx`.
- This closes the previous host-toolchain gap for ARM-family probe images; the
  implementation uses Clang rather than missing GCC cross compilers.
