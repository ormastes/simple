# Domain Research: SimpleOS Multi-Platform Build

Date: 2026-04-20

## 32-bit x86 Baremetal Build Pattern

Common baremetal x86_32 kernels use a dedicated i686 ELF cross target rather than host compiler defaults. The usual shape is:

- compile C with a freestanding target such as `i686-unknown-none-elf`
- pass `-m32` and an i686 CPU baseline
- disable hosted-library assumptions with `-ffreestanding`, `-nostdlib`, `-fno-builtin`, and `-fno-stack-protector`
- compile assembly as 32-bit code and link with ELF32/i386 output
- put a Multiboot1 header near the start of the image for `qemu-system-i386 -kernel`

## Build Infrastructure Pattern

Cross-platform OS builds are less error-prone when target metadata is explicit and data-driven:

- each platform records its compiler target triple, linker script, boot protocol, C sources, ASM sources, and emulator defaults
- C and assembly boot support are compiled into objects before the final kernel link
- hosted compiler artifacts are documented separately from guest OS targets
- aliases such as `x86_32`, `i386`, and `i686` resolve to a single canonical target

## SimpleOS Implication

The SimpleOS catalog should canonicalize the 32-bit x86 lane as `i686-simpleos`, use `i686-unknown-none-elf` for C/ASM boot support, and keep QEMU execution on `qemu-system-i386`. This matches the existing x86_32 Multiboot1 boot sources in `examples/simple_os/arch/x86_32/boot/`.

## Sources

- GNU Multiboot specification: https://www.gnu.org/software/grub/manual/multiboot/multiboot.html
- Clang cross-compilation documentation: https://clang.llvm.org/docs/CrossCompilation.html
- QEMU x86 system emulator documentation: https://www.qemu.org/docs/master/system/target-i386.html
