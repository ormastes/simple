# Cross-Platform Dynload Bootstrap Remaining Plan (2026-07-10)

## Current State

- Linux current-main pure-Simple Stage 2/3 dynload: PASS from a clean cache on
  2026-07-25. LLVM virtual dispatch, PTX float-bit formatting, ELF relocation
  values, and `rt_dict_insert -> rt_dict_set` lowering are covered.
- Historical FreeBSD 14.3 QEMU smoke: PASS. The canonical full lane now uses
  supported FreeBSD 14.4.
- Rust `simple-runtime` and `simple-compiler` host checks: PASS.
- Native macOS and Windows verification remains unresolved. Windows run
  `30151387951` proved Chocolatey LLVM 18 does not ship the `llvm-config`
  required by `llvm-sys`; strict Windows LLVM is therefore not a supported
  bootstrap lane. Multiplatform run `30152376592` also failed Windows LLVM seed
  setup, Windows Cranelift Stage 2 linking, and both native macOS bootstrap
  variants before terminal platform evidence.
- Windows bootstrap now uses Cranelift only. Linux and both macOS architectures
  retain LLVM and Cranelift gates.
- The release workflow no longer installs the incompatible Chocolatey LLVM
  package or runs an optional Windows `llvm-lib` stage. The portability
  contract rejects restoring that false evidence.
- FreeBSD run `30180339652` retained the complete `rust-seed-build.log` and
  proved the seed linker could not find `libffi` or `zstd`. The canonical QEMU
  wrapper now installs both packages and exports FreeBSD's `/usr/local/lib`
  and pkg-config paths. Run `30181046440` then reached seed provenance and
  stopped before log creation because its Perl helper was not installed; the
  wrapper now installs and verifies `perl5`, and fingerprint failures are
  explicit. Terminal Stage 3 and artifact evidence remains open.
- Commit `d3f77e847aa1` routes production `.smf` execution through the real
  loader, resolves `main`, and calls its executable address without the Rust
  delegate. Commit `1c8b26de9b48` adds a real cache reuse/mutation/launcher
  identity scenario and fixes the watcher fallback import cycle. Terminal CI
  evidence remains required before closing the consumer row.

## Remaining Work

1. Run one fresh FreeBSD full verification:

   ```sh
   sh scripts/check/check-freebsd-bootstrap-qemu.shs --full
   ```

   Acceptance: Rust seed/runtime build, Stage 2/3 dynload success, Stage 3
   artifact retrieval, and clean QEMU shutdown.

2. Run native macOS verification on Intel and Apple Silicon where available:

   ```sh
   sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --mode=dynload --no-mcp
   sh scripts/bootstrap/bootstrap-from-scratch.sh --full-cli --mode=dynload --no-mcp
   ```

   Acceptance: LLVM major matches, Homebrew libraries resolve, Stage 2/3 pass,
   and the explicit full CLI passes `-c 'print(1+1)'`.

3. Run native Windows Cranelift verification for MSVC and MinGW/UCRT:

   ```bat
   scripts\bootstrap\bootstrap-windows.cmd --backend=cranelift --full-bootstrap --mode=dynload --no-mcp
   scripts\bootstrap\bootstrap-windows.cmd --backend=cranelift --full-cli --mode=dynload --no-mcp
   ```

   Acceptance: correct target triple, `.exe`/`.lib` artifacts, WFFI DLL symbol
   lookup, Stage 2/3 pass, and explicit full CLI smoke. This remains open after
   run `30152376592`; do not restore a Windows LLVM gate until a pinned,
   compatible seed provider includes `llvm-config`, libraries, and the matching
   ABI, or a separately designed Cranelift-seed to pure-Simple Stage 2 bridge
   reaches the existing dynamic `LLVM-C.dll` loader for Stage 3.

   The prerequisite Cranelift lane still fails at Stage 2 on both Windows
   toolchains (`30178515336`). That run discarded the unresolved-symbol detail
   emitted on linker stdout; the bootstrap linker now retains stdout and
   stderr. Rerun the strict lane and use the recovered symbol evidence before
   changing providers or link arguments.

4. Prove the deployed dynload consumer boundary. The current fast path avoids
   Stage 4 and produces staged/cache artifacts; it must not claim hot deployment
   until the production CLI demonstrably loads the refreshed SMF/native module
   manifest without relinking.

   Acceptance: edit one leaf `.spl`, rebuild only that module, observe a cache
   hit for unchanged modules, and execute the changed behavior through the
   production launcher without replacing the monolithic CLI.

   Implementation is complete. Run the real integration scenario and retain
   it as a release gate only after it proves changed behavior, cache reuse, and
   unchanged launcher identity without mocks or source-text checks.

5. After all native-host gates pass, update the status report, close TODO rows,
   and run the normal verify/release process. Do not use a Rust seed fallback as
   production evidence.

## Ownership

- Platform host lanes: macOS and Windows host operators.
- FreeBSD lane: Linux QEMU operator using the canonical checker.
- Dynload consumer lane: compiler loader/runtime owner.
- Merge owner and final reviewer: bootstrap/compiler maintainer on `main`.
