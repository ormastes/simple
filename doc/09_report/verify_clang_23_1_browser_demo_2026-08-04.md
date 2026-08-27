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
- The final provenance diagnosis traced the missing receipt to a tree restore
  that dropped typed Aetheric background shorthand normalization. The restored
  producer path preserves the base color, full gradient stops and angle, and
  retains unsupported layers as a fail-closed raw witness.
- QEMU and hosted evidence predicates now admit only their legal strong
  material receipts while preserving rendered-backend, 64-hex digest,
  theme/source, and rejection-marker checks. The migration contract passed 5/5
  and both wrappers passed shell syntax.

## Blocking evidence

- Rust `inkwell` remains optional legacy source because its available bindings
  do not support LLVM 23.1; it is no longer reachable from normal bootstrap or
  CI. Production LLVM ownership is the admitted pure-Simple 23.1 provider.
- Pure-Simple runtime execution of the version parser remains unproven because
  the full integration spec timed out and the runner's documented filter was
  rejected.
- A fresh scoped continuation proved and repaired custom-property transport:
  the collector now keeps chained concatenation statically `text`, state
  parsing uses `find_from`, and exact backdrop admission uses bounded ASCII
  byte parsing instead of incomplete freestanding text/integer helpers.
- The retained focused Clang 23.1 guest proves both custom properties, resolved
  Aetheric CSS, exact background/gradient colors, memo color, and
  `backdrop-admission value=true:4:1700`, with no fault.
- Canonical QEMU cycle 1 isolated the admission defect. Cycle 2 cleared it but
  exposed a page fault in the provisional global `rt_any_add` widening; that
  change was reverted. Cycle 3 used the typed producer fix, built 6 modules
  with 725 cached, and reached CPU-entry/font rendering without rejection or
  fault.
- Cycle 3 still failed the 180-second readiness oracle. Serial evidence shows
  repeated 1,048,576-element draw/font arrays (about 8 MiB each) before the
  guest stalls; no desktop/browser-ready, framebuffer, input, or content-delta
  receipts are emitted. This is now the concrete release blocker.
- Therefore framebuffer/font/input/browser-content rendering evidence is not
  complete, and compiler/core/MCP aggregate checks were not run against a
  passing final QEMU input.
- The focused renderer regression spec could not reach assertions because the
  current pure-Simple runner fails parsing the existing multiline import in
  `src/lib/common/web/browser_renderer_protocol.spl`. No seed fallback was used.
- The focused QEMU wrapper contract reached 5 passing cases before existing
  string-interpolation semantic errors (`font_guest_path`, `handled_text`)
  prevented a complete verdict.
- A fourth QEMU run was not attempted because the mandatory three-cycle cap is
  exhausted. The next bounded session must reduce or bound the repeated
  million-element draw/font allocation path and then obtain the canonical
  readiness, framebuffer, input, and browser-content receipts.

## Result

`STATUS: FAIL`

The Clang 23.1 migration and bootstrap lanes are suitable for review. The
SimpleOS rendering gate remains release-blocking because production draw/font
materialization does not finish within the canonical readiness window.
