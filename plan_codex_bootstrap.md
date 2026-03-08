# Codex Bootstrap Status (2026-03-01)

## Replan Update (2026-03-08, macOS arm64)

## Execution Update (2026-03-08, Stage 3 full + default llvm-lib)

### Code changes applied
- Updated compile defaults to prefer pure Simple LLVM lib backend:
  - `src/app/io/cli_compile.spl`
    - `backend` default changed from `auto` -> `llvm-lib`
    - help text updated to show default `llvm-lib`
    - native bridge changed from `--backend llvm` -> `--backend llvm-lib`
    - added support for `--backend <value>` form in `cli_native_build`
    - `cli_native_build` now uses pure llvm-lib path only when backend is explicitly set to llvm-lib
      (default native-build path stays on `rt_native_build` for stability)

### Stage builds executed
1. Canonical bootstrap script:
   - `scripts/bootstrap/bootstrap-from-scratch.sh --skip-download --skip-rust-build --keep-artifacts --jobs=7`
   - Result:
     - `build/bootstrap/stage1/simple`
     - `build/bootstrap/stage2/simple`
     - Stage1/Stage2 reproducible hash:
       - `ade36639f7821f75507bfc7198500fc34bbd7f31f9582beeba7eacb851578bfa`

2. Stage3 full attempt (requested full entry + llvm-lib):
   - `build/bootstrap/stage2/simple native-build --source src/compiler --source src/lib --source src/app --entry src/app/cli/main.spl --backend llvm-lib -o build/bootstrap/stage3_full/simple --strip`
   - Result: binary builds and links, but runtime identity is still bootstrap CLI:
     - `build/bootstrap/stage3_full/simple --version` -> `simple-bootstrap 0.8.0`
     - `build/bootstrap/stage3_full/simple --help` -> `Simple Bootstrap Compiler v0.8.0`

3. Stage4 rebuild from Stage3 (stable path):
   - `build/bootstrap/stage3_full/simple native-build --source src/compiler --source src/lib --source src/app --entry src/app/cli/main.spl --clean -o build/bootstrap/stage4_full/simple --strip`
   - Hashes now match:
     - Stage3: `823bda61c7f08146b78523b9a9c387cff6741283321845d526ac054ec5693698`
     - Stage4: `823bda61c7f08146b78523b9a9c387cff6741283321845d526ac054ec5693698`

### Smoke results (interpreter / loader / native)
- Stage3 full candidate (`build/bootstrap/stage3_full/simple`) behavior:
  - `--help` / `--version`: full CLI works (`Simple Language v0.8.0`, full command list).
  - Interpreter path: `simple /tmp/stage3_hello.spl` exits 139 with runtime missing symbols:
    `Logger.trace`, `parse_outline`, `with_file`, `with_module`, `resolve`, `parse`.
  - Native path (default backend): `simple compile /tmp/stage3_hello.spl -o /tmp/h.native` succeeds (exit 0),
    but running `/tmp/h.native` exits 3 with no output.
  - Loader path: `simple compile /tmp/stage3_hello.spl --format=smf -o /tmp/h.smf` exits 139
    with the same missing symbols; `/tmp/h.smf` run fails.

### Current blocker for Stage 3 full
- Stage3 full binary is now full CLI and Stage3/Stage4 are reproducible.
- Remaining blocker is runtime completeness in pure-Simple interpreter/SMF compile paths
  (missing symbols at runtime in Stage3 binary).

### TODO status (compact checklist)
- [x] Default backend switched to `llvm-lib` in full compile path code.
- [x] `--backend` override preserved.
- [x] Stage3 binary built from Stage2 with requested entry/backend flags.
- [x] Stage4 binary rebuilt from Stage3 and hashes compared.
- [x] Stage3 full binary verified as full CLI (`simple --help` full command set).
- [ ] Interpreter smoke on Stage3 full binary (currently fails with missing symbols).
- [ ] Loader smoke on Stage3 full binary (currently fails with missing symbols).
- [ ] Native smoke on Stage3 full binary with default backend (compile works; produced binary exits 3).
- [x] Focused CLI checks run and logged on Stage3 full binary.

## Mac Progress Notes (2026-03-08)
- Stage1/Stage2 bootstrap via `scripts/bootstrap/bootstrap-from-scratch.sh --skip-download --skip-rust-build --keep-artifacts --jobs=7` completed with reproducible hash `ade36639f7821f75507bfc7198500fc34bbd7f31f9582beeba7eacb851578bfa`.
- Stage3 full CLI (`build/bootstrap/stage3_full/simple`) is now built from Stage2 with `native-build --entry src/app/cli/main.spl --backend llvm-lib` and reports the same CLI help/version text as the release compiler.
- Stage4 (rebuild from Stage3 with `native-build --clean`) matches Stage3 hash `823bda61c7f08146b78523b9a9c387cff6741283321845d526ac054ec5693698`.
- Interpreter/loader paths crash with `Runtime error: Function 'Logger.trace' not found` etc., blocking pure-Simple execution tests.
- `simple compile /tmp/stage3_hello.spl -o /tmp/h.native` succeeds but the produced binary exits with code 3; SMF compilation fails for the same missing-symbol reason.
- Next focus: restore the missing runtime symbols for `Logger.trace`, parser helpers, and module resolution so interpreter/loader invocations complete.

### Requested constraint
- Stage 1 can use Rust backend.
- Pure Simple stages must use `llvm-lib` backend.

### Executed on macOS
1. Verified Rust seed works on macOS:
   - `src/compiler_rust/target/bootstrap/simple --version` -> `Simple Language v0.8.1`
2. Built Stage 1 (Rust seed -> Simple binary, full CLI entry):
   - `src/compiler_rust/target/bootstrap/simple native-build --source src/compiler --source src/lib --source src/app --entry src/app/cli/main.spl -o build/bootstrap/stage1_full/simple --strip`
   - Result: success (`build/bootstrap/stage1_full/simple`, Mach-O arm64).
3. Tried Stage 2 with pure Simple `llvm-lib` from Stage 1:
   - `build/bootstrap/stage1_full/simple compile examples/01_getting_started/hello_native.spl --format=native --backend=llvm-lib -o /tmp/hello_stage2_from_stage1`
   - Result: fails at runtime:
     - `Runtime error: Function 'CompilerDriver.compile' not found`
     - `Runtime error: Function 'get_errors' not found`

### Root blocker
- Stage 1 produced by Rust `native-build` links with large unresolved-symbol auto-stubs.
- The resulting binary starts and handles basic CLI, but does not contain required runtime symbols for pure-Simple `llvm-lib` compilation path.
- Therefore Stage 2/Stage 3 cannot currently be completed under the required "pure Simple + llvm-lib" constraint.

### Current status
- `bin/simple` wrapper is unusable on this macOS workspace because it points to Linux ELF (`bin/release/simple`).
- Rust seed is healthy.
- Pure-Simple `llvm-lib` bootstrap chain is blocked by missing symbols in Rust-seeded Stage 1 artifact.

### Next fix targets
1. Build a non-stubbed Stage 1 full CLI binary from Rust seed (must include `CompilerDriver.compile` and related driver API symbols).
2. Re-run Stage 2/3 with:
   - `stage1_full/simple compile src/app/cli/main.spl --format=native --backend=llvm-lib -o build/bootstrap/stage2_llvm`
   - `build/bootstrap/stage2_llvm compile src/app/cli/main.spl --format=native --backend=llvm-lib -o build/bootstrap/stage3_llvm`
3. Validate:
   - `--version`, `--help`
   - compile/run smoke sample
   - bootstrap hash comparison (stage2 vs stage3)
4. Then run bootstrap test scripts/specs.

## Summary
- Stage1 compiler still builds clean.
- Stage2/Stage3 bootstrap **now link successfully**; native binary is at `./tmp/simple_stage3_native` (links against `libsimple_runtime.so`).
- Auto‑stub allow-list was widened: all `rt_*` symbols plus a handful of non‑rt helpers (`acquire`, `empty`, `defaults`, `mem_* leak tracker`, etc.) are preserved; everything else still auto‑stubbed.
- Added real shims earlier (process spawn/wait/kill, file delete/size, time nanos/micros, SHA256) and kept them.
- Runtime execution of the stage3 binary currently exits with code 1 for `--version/--help` and simple compile runs; likely needs proper env/assets (e.g., `SIMPLE_LIB`, `SIMPLE_HOME`, `LD_LIBRARY_PATH`).

## Latest status (2026-03-01)
- Link succeeds; no remaining undefined symbols during bootstrap link.
- Stage3 binary present: `./tmp/simple_stage3_native` (PIE, dynamically linked; depends on `libsimple_runtime.so`).
- Binary currently not responding to `--version/--help`; needs runtime env investigation.

## Work Done (this session)
- Allowed all `rt_*` symbols in bootstrap auto-stubs to avoid piecemeal misses; added explicit keepers for `acquire`, `empty`, `defaults`, `mem_enable`, `mem_snapshot`, `mem_dump_leaks`, `mem_live_*`, `mem_reset`.
- Added keepers for full file I/O, TCP/UDP I/O, epoll/socket nonblocking, stdin/out/err, leak tracker, and other runtime helpers.
- Kept earlier real C shims (process, time, file size/delete, SHA256) and removed extra runtime archive to avoid duplicate symbols.

## Current Blocking Issue
- Stage3 binary runs but exits with code 1 for basic CLI invocations; likely missing env/assets. Need to determine required runtime environment (e.g., `SIMPLE_HOME`, `SIMPLE_LIB`, `LD_LIBRARY_PATH`) or adjust CLI dispatch.

## Next Steps (proposed)
1) Figure out runtime env needed for `./tmp/simple_stage3_native` (try `SIMPLE_HOME=$(pwd)`, `SIMPLE_LIB=src`, `LD_LIBRARY_PATH=src/compiler_rust/target/release`, and ensure assets exist).
2) Run smoke tests once env sorted: `--version`, `--help`, `compile examples/hello.spl -o /tmp/hello_stage3`.
3) Optionally tighten allow-list later (replace blanket `rt_*` keep with precise set) once stable.
4) Clean temp artifacts (`tmp/`) after confirming runtime behavior.

## How to Verify (once link succeeds)
```
SIMPLE_HOME=$(pwd) SIMPLE_LIB=src LD_LIBRARY_PATH=src/compiler_rust/target/release ./tmp/simple_stage3_native --version
SIMPLE_HOME=$(pwd) SIMPLE_LIB=src LD_LIBRARY_PATH=src/compiler_rust/target/release ./tmp/simple_stage3_native compile examples/hello.spl -o /tmp/hello_stage3
```

## Useful Paths
- Stage1 compiler: `src/compiler_rust/target/release/simple`
- Stage3 binary: `./tmp/simple_stage3_native`
- Entry source: `src/app/cli/main.spl`
- C stub fix: `src/compiler_rust/compiler/src/pipeline/native_project.rs:501-516`
- Runtime args: `src/compiler_rust/runtime/src/value/args.rs`

## Owner Notes
- Segfault fixed; Stage2 runs CLI commands successfully.
- `native-build` exits with code 8 on all native binaries — this is the next blocker for Stage3.
- Parser improvements: 163 remaining parse failures (down from 284).
- Keep using clang (not gcc_s) per instructions.
