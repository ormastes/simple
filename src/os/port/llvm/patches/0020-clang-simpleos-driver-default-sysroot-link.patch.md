# Clang SimpleOS Driver Default Sysroot Link Patch

## Problem

The canonical cross `clang` could compile `hello.c` with `-c`, but a normal
driver link:

```sh
clang --target=x86_64-unknown-simpleos hello.c -o hello.elf
```

failed because the SimpleOS toolchain only added sysroot paths when callers
passed `--sysroot=...`. The driver therefore invoked `ld.lld` without `crt0.o`,
the SimpleOS linker script, `-L <sysroot>/lib`, or the staged compiler-rt
builtins directory.

## Patch

In `clang/lib/Driver/ToolChains/SimpleOS.cpp`:

- derive the default sysroot from the installed driver path
  (`build/os/llvm/cross-<triple>/bin` -> `build/os/sysroot`),
- add `--sysroot`, `-T <sysroot>/share/simpleos/simpleos.ld`, and
  `<sysroot>/lib/crt0.o` to the linker job,
- add `-L <sysroot>/lib` and
  `-L <sysroot>/lib/clang/20/lib/<triple>`,
- link `-lclang_rt.builtins-<arch>` instead of the unsuffixed builtins name,
- use the same default sysroot for C and C++ system include paths.
