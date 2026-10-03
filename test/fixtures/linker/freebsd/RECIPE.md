# FreeBSD ABI metadata fixture

`abi_note_x64.o` was assembled with Ubuntu LLVM 21 for
`x86_64-unknown-freebsd`. It contains an allocated `.note.tag` and no code.
`llvm-readelf -h -n` independently reports ELFOSABI FreeBSD and an ABI tag
descriptor of 1400000. That version is fixture data, not a host qualification.

Assembler input:

```asm
.section .note.tag,"a",@note
.p2align 2
.long 8
.long 4
.long 1
.asciz "FreeBSD"
.long 1400000
```

Command: `clang --target=x86_64-unknown-freebsd -c freebsd_note.s -o abi_note_x64.o`.

Hosted startup ordering follows [Clang's FreeBSD toolchain](https://clang.llvm.org/doxygen/FreeBSD_8cpp_source.html).
Brand and note interpretation are owned by [FreeBSD's ELF image activator](https://cgit.freebsd.org/src/tree/sys/kern/imgact_elf.c).

## Hosted main fixtures

`main_x64.o` and `main_a64.o` define `main`, return 42, and have no libc or
runtime references. They exercise the installed FreeBSD CRT and loader through
the internal hosted linker. They do not supply a replacement `_start`.

AMD64 assembly:

```asm
.text
.globl main
.type main,@function
main:
    movl $42, %eax
    ret
.size main, .-main
.section .note.GNU-stack,"",@progbits
```

ARM64 assembly uses `mov w0, #42` followed by `ret`, with the same directives.
Build with `clang --target=x86_64-unknown-freebsd -c freebsd_main_x64.s -o main_x64.o`
and `clang --target=aarch64-unknown-freebsd -c freebsd_main_a64.s -o main_a64.o`.
LLVM 21 produced both objects; native execution remains unverified.
