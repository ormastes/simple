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

These are real MH_OBJECT inputs. The linker result must be MH_EXECUTE, with
mapped segments and LC_UNIXTHREAD; object emission is not executable evidence.
The x86_64 call patch is +3 after 4-byte input-section alignment. The ARM64
BL patch is +16 bytes. ARM64 ADRP targets the data segment, and LDR encodes its
scaled page offset. Neither fixture requires dyld or TLS. Native Darwin loader
admission, including signing policy, remains separate from image construction.
