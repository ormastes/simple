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
- Normal Rust bootstrap/CI is now Cranelift-only and fails closed for the
  legacy `llvm`/`llvm-lib` modes. The focused isolation contract passed, the
  normal Cargo graph contains no `inkwell`/`llvm-sys`, and the offline locked
  `simple-driver` check passed.
- The x86_64 freestanding runtime now provides a real `rt_array_sort`; its
  Clang 23.1 object, strong symbol, nontrivial disassembly, and 3/3 focused
  contract passed.
- Concrete `SoftwareBackend` routing replaced the native duck-dispatch trap
  across the browser Draw IR offscreen path; its focused contract passed 3/3.

## Blocking evidence

- Rust `inkwell` remains optional legacy source because its available bindings
  do not support LLVM 23.1; it is no longer reachable from normal bootstrap or
  CI. Production LLVM ownership is the admitted pure-Simple 23.1 provider.
- Pure-Simple runtime execution of the version parser remains unproven because
  the full integration spec timed out and the runner's documented filter was
  rejected.
- The continuation's fullscreen QEMU gate exhausted its three-cycle cap:
  1. the repaired sort provider reached active web rendering, but the fixed
     60-second readiness window stopped the still-progressing 4K frame;
  2. the extended window exposed and precisely symbolized the software
     offscreen trait-dispatch `ud2` in `Engine2D.clear`;
  3. concrete dispatch removed that trap and rendered Browser, Hello, and the
     launchable Clang surface, then the compositor rejected each window's
     content provenance (`status=engine2d_rendered backend=software material=`)
     and marked them degraded before readiness/capture.
- Therefore framebuffer/font/input/browser-content rendering evidence is not
  complete, and compiler/core/MCP aggregate checks were not all green.

## Result

`STATUS: FAIL`

The migration and bootstrap lanes are suitable for review, but the rendering
gate remains release-blocking. The next scoped session must repair the missing
software content-material provenance before another QEMU attempt.
