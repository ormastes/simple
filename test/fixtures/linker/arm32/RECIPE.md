# ARM32 linker fixtures

The checked-in objects are deterministic LLVM Cortex-M3 ELF32 inputs. The
main fixture uses `.reloc` deliberately because LLVM selects the wider
`R_ARM_THM_PC12` for an unresolved symbolic `ldr` on Cortex-M3:

```sh
clang --target=arm-none-eabi -mcpu=cortex-m3 -mthumb -c thumb_pc8_main.s -o thumb_pc8_main.o
clang --target=arm-none-eabi -mcpu=cortex-m3 -mthumb -c thumb_pc12_main.s -o thumb_pc12_main.o
clang --target=arm-none-eabi -mcpu=cortex-m3 -mthumb -c thumb_pc8_target.s -o thumb_pc8_target.o
llvm-readelf -r thumb_pc8_main.o
```

`thumb_pc8_main.o` carries the explicit AAELF32 `R_ARM_THM_PC8` oracle against
the provider object. `thumb_pc12_main.o` records LLVM's natural Cortex-M3
choice for the unresolved symbolic literal load.

With `ld.lld --image-base=0 -Ttext=0x1000 --oformat=binary`, the leading
linked bytes are `01 48 70 47` for PC8 and `df f8 04 00 70 47` for PC12.
