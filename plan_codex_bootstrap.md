# Codex Bootstrap Status (2026-03-01)

## Replan Update (2026-03-08, macOS arm64)

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
