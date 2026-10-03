# RV64 static linker fixtures

Produced with Ubuntu clang and LLD 21.1.8, `llvm-ar`, through WSL Ubuntu.
The assembly uses LP64 soft-float RV64IMAC. Explicit `.reloc` directives keep
cross-object branch/compressed-branch encodings from being assembler-expanded.

```sh
clang --target=riscv64-unknown-linux-gnu -march=rv64imac -mabi=lp64 -c start.s -o start.o
clang --target=riscv64-unknown-linux-gnu -march=rv64imac -mabi=lp64 -c provider.s -o provider.o
clang --target=riscv64-unknown-linux-gnu -march=rv64imac -mabi=lp64 -c relax.s -o relax.o
llvm-ar rcs libprovider.a provider.o
llvm-readelf -r -h start.o provider.o relax.o
ld.lld --no-relax -static -e _start start.o provider.o -o oracle.elf
qemu-riscv64 ./oracle.elf # expected exit 42
```

Fixture compilation and relocation census ran during authoring. The commands
for LLD output and QEMU execution above are recipes, not claims of execution.
Simple acceptance execution is pending an admitted self-hosted runtime.

`start.o` has fourteen relocations: PCREL_HI20 (2), PCREL_LO12_I (2),
PCREL_LO12_S, GOT_HI20, HI20, LO12_I, LO12_S, CALL_PLT, BRANCH, RVC_BRANCH,
RVC_JUMP and JAL. `relax.o` isolates CALL_PLT plus RELAX without ALIGN padding.
