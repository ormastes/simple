# Mach-O static-link fixtures

Compile these assembly inputs with LLVM clang (no Apple SDK or runtime needed):

```text
clang --target=x86_64-apple-macos11 -c start_x64.s -o start_x64.o
clang --target=x86_64-apple-macos11 -c provider_x64.s -o provider_x64.o
clang --target=arm64-apple-macos11 -c start_a64.s -o start_a64.o
clang --target=arm64-apple-macos11 -c provider_a64.s -o provider_a64.o
llvm-ar --format=darwin rcs provider_x64.a provider_x64.o
llvm-ar --format=gnu rcs provider_a64.a provider_a64.o
llvm-readobj --file-headers --sections --symbols --relocations start_x64.o start_a64.o
```

Compile `mid_x64.s`, `leaf_x64.s`, `weak_x64.s`, `common_x64.s`, and
`common_large_x64.s` with the same x86_64 command. Build the transitive archive
with `llvm-ar --format=darwin rcs chain_x64.a leaf_x64.o mid_x64.o` (leaf first,
so the entry's initially unresolved `_helper` cannot accidentally select it).

These are real MH_OBJECT inputs. The linker result must be MH_EXECUTE, with
mapped segments and LC_UNIXTHREAD; object emission is not executable evidence.
The x86_64 call patch is +3 after 4-byte input-section alignment. The ARM64
BL patch is +16 bytes. ARM64 ADRP targets the data segment, and LDR encodes its
scaled page offset. Neither fixture requires dyld or TLS. Native Darwin loader
admission, including signing policy, remains separate from image construction.

Wire authorities: [Apple loader.h](https://github.com/apple-oss-distributions/xnu/blob/main/EXTERNAL_HEADERS/mach-o/loader.h)
defines executable/segment/thread commands; [LLVM MachO.h](https://llvm.org/doxygen/BinaryFormat_2MachO_8h_source.html)
defines relocation and thread-state records. Hosted ARM64 signing is a separate
gate, illustrated by [LLD's ad-hoc signing tests](https://github.com/llvm/llvm-project/blob/main/lld/test/MachO/adhoc-codesign.s).
