# RV64 static linker fixtures

Produced with Ubuntu clang and LLD 21.1.8, `llvm-ar`, through WSL Ubuntu.
The assembly uses LP64 soft-float RV64IMAC. Explicit `.reloc` directives keep
cross-object branch/compressed-branch encodings from being assembler-expanded.

```sh
clang --target=riscv64-unknown-linux-gnu -march=rv64imac -mabi=lp64 -c start.s -o start.o
clang --target=riscv64-unknown-linux-gnu -march=rv64imac -mabi=lp64 -c provider.s -o provider.o
clang --target=riscv64-unknown-linux-gnu -march=rv64imac -mabi=lp64 -c relax.s -o relax.o
clang --target=riscv64-unknown-linux-gnu -march=rv64imac -mabi=lp64 -c arithmetic.s -o arithmetic.o
llvm-ar rcs libprovider.a provider.o
llvm-readelf -r -h start.o provider.o relax.o
ld.lld --no-relax -static -e _start start.o provider.o -o oracle.elf
qemu-riscv64 ./oracle.elf # expected exit 42
```

Fixture compilation and relocation census ran during authoring. LLD also
successfully linked start/provider with `--no-relax`; readelf confirmed ELF64,
EM_RISCV, ET_EXEC and e_flags=RVC. QEMU execution is pending: qemu-riscv64 was
not on WSL Ubuntu PATH. LLD output is fixture validation, not Simple evidence.
Simple acceptance execution is pending an admitted self-hosted runtime.

`start.o` has fourteen relocations: PCREL_HI20 (2), PCREL_LO12_I (2),
PCREL_LO12_S, GOT_HI20, HI20, LO12_I, LO12_S, CALL_PLT, BRANCH, RVC_BRANCH,
RVC_JUMP and JAL. `relax.o` isolates CALL_PLT plus RELAX without ALIGN padding.

`arithmetic.o` contains seventeen relocations: an absolute pointer retains the
data section; ADD/SUB pairs cover 8/16/32/64-bit fields; SET6/SUB6 preserve the
upper two bits; SET8/16/32, PCREL32, PLT32 and GOT32_PCREL cover data fields.

Current static-driver boundary: no ALIGN padding deletion, instruction-size
relaxation, ULEB128 relocation pairs, or .riscv.attributes merge. RV32 ELF,
dynamic/PIE and TLS output remain unsupported. Native execution and the Simple
acceptance run are pending. Arithmetic/branch encodings follow the
[RISC-V psABI](https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc)
and [LLVM LLD implementation](https://llvm.googlesource.com/llvm-project/lld/+/6ef5ac64475f61262e794c705a06f0c0ffe769dd/ELF/Arch/RISCV.cpp).
