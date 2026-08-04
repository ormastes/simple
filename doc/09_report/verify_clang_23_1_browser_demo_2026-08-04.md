# Verification: Clang 23.1 Browser Demo Migration

## Passing evidence

- Signed `llvmorg-23.1.0-rc2` tag commit `561093d9...` built Clang, LLD,
  llvm-ar, llvm-objcopy and llvm-config for X86, AArch64, RISC-V and WebAssembly.
- Coherent provider admission rejected host LLVM 22.1 and admitted only 23.1.
- The authorized `build/native_probe/simple` no-stub native smoke passed.
- Clang 23.1 compiled production SimpleOS CRT; matching llvm-ar and LLD
  archived/linked valid x86-64 artifacts with retained hashes.
- Browser client and isolated libc built with 23.1, produced a valid x86-64
  ELF with resolved `getpid`, and staged byte-for-byte as `BROWSMF.SMF`.
- Focused guest-toolchain spec passed 3/3; migration contract passed 5/5;
  working/staged direct-runtime guards passed before final documentation edits.
- Provider builder contract, shell syntax, diff whitespace, and doc layout
  checks passed.

## Blocking evidence

- Rust `inkwell` 0.9 and `llvm-sys` 221 support only through LLVM 22. The
  optional Rust in-process LLVM backend cannot truthfully migrate to 23.1.
- Pure-Simple runtime execution of the version parser remains unproven because
  the full integration spec timed out and the runner's documented filter was
  rejected.
- Fullscreen QEMU exhausted its three-cycle cap:
  1. provider lacked llvm-objcopy, so the kernel remained ELF64;
  2. after adding llvm-objcopy, `native_probe/simple` booted through app
     materialization but halted on fabricated `rt_array_sort`;
  3. an externally validated prior Phase kernel staged the new browser but did
     not reach current scanout/desktop readiness.
- Therefore framebuffer/font/input/browser-content rendering evidence is not
  complete, and compiler/core/MCP aggregate checks were not all green.

## Result

`STATUS: FAIL`

The feature branch is suitable for review and continued integration, not a
release. No QEMU retry beyond the mandatory three-cycle cap is authorized in
this session.
