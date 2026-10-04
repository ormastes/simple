# RV64 static initial-exec fixtures

The checked-in `.o` and `.a` files are real ELF64 relocatable inputs, produced
with Ubuntu clang/LLVM 21. They are not Simple runtime evidence.

From this directory in WSL Ubuntu:

```sh
clang --target=riscv64-unknown-linux-gnu -march=rv64ima -mabi=lp64 -c tls_initial_exec.s -o tls_initial_exec.o
clang --target=riscv64-unknown-linux-gnu -march=rv64ima -mabi=lp64 -c tls_initial_exec_provider.s -o tls_initial_exec_provider.o
llvm-ar rcs libtls_initial_exec.a tls_initial_exec_provider.o
ld.lld --no-relax -static -e _start tls_initial_exec.o tls_initial_exec_provider.o -o /tmp/item4-riscv-ie-oracle.elf
llvm-readelf -s -l -x .got /tmp/item4-riscv-ie-oracle.elf
llvm-objdump -d /tmp/item4-riscv-ie-oracle.elf
clang --target=riscv64-unknown-linux-gnu -march=rv64ima -mabi=lp64 -c tls_initial_exec_residue_provider.s -o tls_initial_exec_residue_provider.o
clang --target=riscv64-unknown-linux-gnu -march=rv64ima -mabi=lp64 -c tls_initial_exec_padded.s -o tls_initial_exec_padded.o
clang --target=riscv64-unknown-linux-gnu -march=rv64ima -mabi=lp64 -c tls_initial_exec_mixed.s -o tls_initial_exec_mixed.o
```

Observed independent LLD output: TLS symbols have offsets 4096, 4128, 4160;
PT_TLS has file extent 4136, memory extent 4168 and alignment 64. The three
IE GOT entries contain those offsets; the repeated reference uses the first
slot. The first paired low instruction is eight bytes after its AUIPC,
exercising label association rather than adjacency. The spec decodes its
actual output addresses; it does not assume LLD's section layout.

The [published RISC-V psABI](https://riscv-non-isa.github.io/riscv-elf-psabi-doc/)
requires zero addends for TLS_GOT_HI20 and its PCREL_LO12 pair. Initial-exec
slots contain TP offsets, not virtual addresses.

The residue provider retains initialized offsets 4096/4128 but uses alignment
8, while `.tbss` requires 64. The original and padded text inputs differ by
eight bytes. The spec requires at least one output to have a nonzero TLS
start residue and independently includes that residue in GOT TP offsets.
[LLD's TP offset implementation](https://llvm.googlesource.com/llvm-project/lld/+/c49af813ca6db8f8c74529efcc407ac012a0c231/ELF/InputSection.cpp)
establishes this RISC-V rule.

The mixed fixture adds a normal GOT reference to an ordinary data symbol.
Independent LLD inspection also succeeded for this fixture: three TLS slots
contain 4096/4128/4160, while the fourth contains `ie_plain`'s virtual address.
This is coexistence coverage, not a claim that ordinary GOT references to TLS
symbols are ABI-admitted.

Only fixture construction and external LLVM inspection ran. No fixture
executable or Simple spec was executed.
