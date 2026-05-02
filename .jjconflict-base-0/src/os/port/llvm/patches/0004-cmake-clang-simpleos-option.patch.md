# 0004 — `CLANG_SIMPLEOS_EMBED_LLD` CMake option

Adds a build-time toggle to the clang CMake configuration so a single
`clang` binary can act as its own linker for `*-simpleos` targets. This
is the CMake half of patch 0003 (which provides the C++ driver hunk).

## Rationale

SimpleOS ships a stripped userland — we don't want to install a separate
`ld.lld` in every sysroot. Linking LLD in as a library lets `clang -target
x86_64-unknown-simpleos hello.c -o hello` do codegen **and** link in a
single process, matching the way a lot of other bare-metal toolchains
operate (Zig, embedded GCC distros, etc.). Default is OFF so upstream-
style distro builds are unaffected.

## Target file

`clang/CMakeLists.txt` — near the other `option(CLANG_* …)` declarations
(search for `option(CLANG_BUILD_EXAMPLES` for a good anchor).

## Hunk

```cmake
option(CLANG_SIMPLEOS_EMBED_LLD
       "Embed LLD as a library for *-simpleos targets (enables static clang)"
       OFF)

if(CLANG_SIMPLEOS_EMBED_LLD)
    # LLD must be built as part of this project — enforce it here so the
    # failure mode is "CMake error" not "undefined symbol at link time".
    if(NOT "lld" IN_LIST LLVM_ENABLE_PROJECTS)
        message(FATAL_ERROR
            "CLANG_SIMPLEOS_EMBED_LLD=ON requires 'lld' in LLVM_ENABLE_PROJECTS")
    endif()
    target_compile_definitions(clang PRIVATE CLANG_SIMPLEOS_EMBED_LLD)
    target_link_libraries(clang PRIVATE lldELF lldCommon)
endif()
```

## Enable / test

```bash
cmake -G Ninja -S llvm -B build \
      -DLLVM_ENABLE_PROJECTS='clang;lld' \
      -DCLANG_SIMPLEOS_EMBED_LLD=ON \
      -DCMAKE_BUILD_TYPE=Release
ninja -C build clang
./build/bin/clang -target x86_64-unknown-simpleos -v hello.c -o hello
# Expect the driver to invoke the in-process LLD instead of spawning ld.lld.
```

## Size impact

Embedding `lldELF` + `lldCommon` adds roughly **35–45 MB** to the
release-mode `clang` binary (Linux x86_64, LLVM 19). On debug builds
the number is closer to 120 MB. Keep the option OFF for distro builds.

## Follow-up

Patch 0003 contains the matching `clang/tools/driver/driver.cpp` change
that dispatches to `lld::elf::link` when the macro is defined.
