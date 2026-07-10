# Cross-Platform Dynload Bootstrap Remaining Plan (2026-07-10)

## Current State

- Linux pure-Simple dynload Stage 2/3: PASS in 54 seconds; no Cargo and no
  Stage 4 relink.
- FreeBSD 14.3 QEMU smoke: PASS.
- Rust `simple-runtime` and `simple-compiler` host checks: PASS.
- Portable macOS/Windows paths are implemented but not executed on native
  hosts.
- Full FreeBSD verification reached the mandatory three-cycle cap after
  exposing rsync duplication, monolithic Stage 4 cost, and stale QEMU startup
  state. All three defects are patched; the final full run remains pending.

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

3. Run native Windows verification for MSVC and MinGW/UCRT:

   ```bat
   scripts\bootstrap\bootstrap-windows.cmd --full-bootstrap --mode=dynload --no-mcp
   scripts\bootstrap\bootstrap-windows.cmd --full-cli --mode=dynload --no-mcp
   ```

   Acceptance: correct target triple, `.exe`/`.lib` artifacts, WFFI DLL symbol
   lookup, Stage 2/3 pass, and explicit full CLI smoke.

4. Prove the deployed dynload consumer boundary. The current fast path avoids
   Stage 4 and produces staged/cache artifacts; it must not claim hot deployment
   until the production CLI demonstrably loads the refreshed SMF/native module
   manifest without relinking.

   Acceptance: edit one leaf `.spl`, rebuild only that module, observe a cache
   hit for unchanged modules, and execute the changed behavior through the
   production launcher without replacing the monolithic CLI.

5. After all native-host gates pass, update the status report, close TODO rows,
   and run the normal verify/release process. Do not use a Rust seed fallback as
   production evidence.

## Ownership

- Platform host lanes: macOS and Windows host operators.
- FreeBSD lane: Linux QEMU operator using the canonical checker.
- Dynload consumer lane: compiler loader/runtime owner.
- Merge owner and final reviewer: bootstrap/compiler maintainer on `main`.
