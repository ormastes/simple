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
