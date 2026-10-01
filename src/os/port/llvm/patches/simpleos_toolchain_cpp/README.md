# SimpleOS clang Driver ToolChain — fork patch guidance

This directory does **not** ship a patch bundle. It is maintainer guidance
for adding a first-class `SimpleOS` toolchain class to the vendored LLVM
fork used by the SimpleOS build.

- **Upstream fork:** <https://github.com/ormastes/llvm-project>
- **Branch:** `simpleos`
- **Plan reference:** item A3 in the SimpleOS LLVM port plan.

## Why a ToolChain class

`build.shs` (stage 2, `cross`) configures clang with
`LLVM_DEFAULT_TARGET_TRIPLE=<triple>-unknown-simpleos` and
`SIMPLEOS_SYSROOT`. At driver run time, however, clang routes unknown OS
triples through the generic `Generic_ELF` toolchain, which:

- ignores our resource-dir layout
  (`lib/clang/<ver>/lib/<triple>/libclang_rt.builtins-*.a`),
- does not inject the SimpleOS crt0 object,
- does not select `lld` by default, and
- does not honour the SimpleOS linker script.

A dedicated `clang::driver::toolchains::SimpleOS` class fixes all four
points and lets A4/A5 stage builtins into a location where the driver
will actually find them.

## Files to add in the fork

Under `clang/lib/Driver/ToolChains/` on the `simpleos` branch:

1. **`SimpleOS.h`** — declares `class SimpleOS : public Generic_ELF`.
   Override `GetCXXStdlibType`, `GetDefaultLinker` (`return "lld";`),
   `AddClangSystemIncludeArgs`, `AddClangCXXStdlibIncludeArgs`,
   `getCompilerRTPath`, `IsIntegratedAssemblerDefault` (`return true;`),
   `isPICDefault`, `isPIEDefault`, `isPICDefaultForced`,
   `HasNativeLLVMSupport` (`return true;`), and `getRuntimeLibType`
   (`return ToolChain::RLT_CompilerRT;`).

2. **`SimpleOS.cpp`** — implements the above. Key points:
   - `AddClangSystemIncludeArgs`: prepend `<sysroot>/include` and
     `<sysroot>/include/c++/v1` (when libc++ is later enabled).
   - `getCompilerRTPath`: return `<resource-dir>/lib/<triple>/`, which
     matches what A5 stages into
     `build/os/sysroot/lib/clang/<ver>/lib/<triple>/`.
   - `Linker::ConstructJob`: add a private `Tool` that invokes `ld.lld`
     with `-T <sysroot>/lib/simpleos.lds`, the crt0 object from the
     sysroot, and `-lsimpleos_c -lclang_rt.builtins-<arch>`.
   - Recognised triples: `x86_64-unknown-simpleos`,
     `aarch64-unknown-simpleos`, `riscv64gc-unknown-simpleos`,
     `riscv32imac-unknown-simpleos`.

## Driver hook-up

In `clang/lib/Driver/Driver.cpp`, extend `Driver::getToolChain` to route
the new OS kind to `SimpleOS`. This requires adding `Triple::SimpleOS`
(or reusing an existing custom OS slot) in
`llvm/include/llvm/TargetParser/Triple.h` and
`llvm/lib/TargetParser/Triple.cpp`:

- Add `SimpleOS` to the `OSType` enum.
- Parse `"simpleos"` in `parseOS`.
- Print `"simpleos"` in `getOSTypeName`.

Register the new source files in `clang/lib/Driver/CMakeLists.txt`.

## Build + consume

After merging the above into the `simpleos` branch of the fork:

```sh
LLVM_SRC=~/llvm-project sh src/os/port/llvm/build.shs host-tools
SIMPLE_TARGET=x86_64-unknown-simpleos \
    sh src/os/port/llvm/build.shs cross
SIMPLE_TARGET=x86_64-unknown-simpleos \
    sh src/os/port/llvm/build.shs compiler-rt
```

With the ToolChain class in place, the resulting
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/clang` auto-finds the
staged builtins at
`build/os/sysroot/lib/clang/19/lib/x86_64-unknown-simpleos/`.

## Out-of-scope for this directory

No `.patch` files, no prebuilt binaries, no auto-apply script. The fork
owns the source of truth — this README only exists to keep the contract
between the SimpleOS port and the fork documented in-tree.
