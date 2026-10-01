<!-- codex-research -->
# Domain Research: LLVM/Clang 23.1

## Release status on 2026-08-04

LLVM 23.1.0 is not stable yet. The official release schedule places final 23.1.0 on 2026-08-25. The newest signed tag available during research is `llvmorg-23.1.0-rc2`, released 2026-07-28. Current implementation evidence must therefore say `23.1.0-rc2`; it must not relabel a snapshot or release candidate as final.

Sources:

- [Official LLVM releases](https://github.com/llvm/llvm-project/releases)
- [LLVM 23.1.0 rc1 announcement](https://discourse.llvm.org/t/llvm-23-1-0-rc1-released/91369)
- [Clang release notes](https://github.com/llvm/llvm-project/blob/main/clang/docs/ReleaseNotes.rst)

## Distribution and naming

Official archives install normally unversioned `clang`, `clang++`, `ld.lld`, `llc`, `opt`, and related tools within a versioned prefix. Linux apt snapshots may expose `clang-23`; Homebrew currently provides stable LLVM 22 and no `llvm@23`; Windows uses `clang.exe`. Discovery must accept configurable absolute paths and verify `--version`, not assume a versioned executable name.

The current-host reproducible strategy is a source build from the signed rc2 tag into an isolated prefix, retaining tag/commit, compiler version, paths, and hashes. Stable 23.1 can replace rc2 without changing the major/minor admission contract.

## Target and compatibility findings

- Clang cross compilation requires explicit target, CPU/ABI, sysroot, and linker choices. The repository must test its exact custom triples rather than infer support from host compilation. See [Clang Cross Compilation](https://clang.llvm.org/docs/CrossCompilation.html).
- LLVM MC supports ELF emission for X86, AArch64, and RISC-V. RISC-V RV32I/RV64I are supported; RV128 is not. See [LLVM Code Generator](https://llvm.org/docs/CodeGenerator.html) and [RISC-V usage](https://llvm.org/docs/RISCVUsage.html).
- Freestanding Clang may still emit `memcpy`, `memmove`, and `memset`; SimpleOS must provide them. See the [Clang Users Manual](https://clang.llvm.org/docs/UsersManual.html).
- LLVM bitcode is forward-readable by newer LLVM under policy, but downgrade from LLVM 23 products to LLVM 18 tools is unsupported; textual IR has no compatibility promise. The compiler, optimizer, code generator, linker, and library binding must migrate as a family.
- No removed flag affecting the browser demo's `-ffreestanding`, `-nostdlib`, `-fno-builtin`, section-GC, or custom-target use was found in current release notes. Compile/link/boot evidence remains mandatory because the notes are prerelease.

## Critical conclusion

Clang 23.1 does not appear to remove a required SimpleOS target capability. The blocking problems are release availability, package naming, coherent tool-family admission, Rust binding support, and actual cross/freestanding regression coverage—not an identified dropped X86/AArch64/RISC-V feature.
