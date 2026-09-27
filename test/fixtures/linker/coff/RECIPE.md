# AMD64 COFF linker fixtures

The checked-in objects are deterministic LLVM Windows-MSVC inputs:

```sh
clang-cl /nologo /c /O1 /Gy /Gw /Brepro /Zl /Fowindows_corpus_main.obj windows_corpus_main.c
clang-cl /nologo /c /O1 /Gy /Gw /Brepro /Zl /Fowindows_corpus_provider.obj windows_corpus_provider.c
clang-cl --target=aarch64-pc-windows-msvc /nologo /c /O1 /Gy /Gw /Brepro /Zl /Fowindows_arm64_relocs.obj windows_arm64_relocs.c
lld-link /entry:_start /subsystem:console /nodefaultlib /out:windows_corpus.exe windows_corpus_main.obj windows_corpus_provider.obj
llvm-readobj --file-headers --sections --relocations windows_corpus_main.obj windows_corpus_provider.obj
llvm-readobj --file-headers --sections --coff-basereloc windows_corpus.exe
```

The pair exercises real COMDAT text/data, cross-object `REL32`, exception
metadata, entry resolution, and PE image construction without CRT imports.
The ARM64 census object pins the production compiler's `BRANCH26`,
`PAGEBASE_REL21`, `PAGEOFFSET_12A`, `PAGEOFFSET_12L`, and `ADDR32NB` set.
