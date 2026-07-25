# Cross-Platform Dynload Bootstrap Remaining Plan (2026-07-10)

## Current State

- Linux current-main pure-Simple Stage 2/3 dynload: PASS from a clean cache on
  2026-07-25. LLVM virtual dispatch, PTX float-bit formatting, ELF relocation
  values, and `rt_dict_insert -> rt_dict_set` lowering are covered.
- Historical FreeBSD 14.3 QEMU smoke: PASS. The canonical full lane now uses
  supported FreeBSD 14.4.
- Rust `simple-runtime` and `simple-compiler` host checks: PASS.
- Native macOS and Windows verification is active in GitHub Actions. Windows
  run `30148705502` is non-cancelling; isolated multiplatform run
  `30149462707` covers Intel/Apple Silicon macOS and both Windows backends.
- FreeBSD run `30147237924` proved the previous shell user-data disabled
  firstboot jobs too late. Commits `05796f7883b0` and `d3f77e847aa1` select
  supported 14.4 and write per-service `rc.conf.d` flags through early
  cloud-config. Current full run `30149458196` is queued.
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
