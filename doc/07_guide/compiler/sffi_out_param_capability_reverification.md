# Re-verification recipe: `&mut` out-param capability check (seed HIR)

Bug: `doc/08_tracking/bug/sffi_out_param_capability_violation_blocks_stage2_2026-08-27.md`
Fix: `src/compiler_rust/compiler/src/hir/lower/expr/calls.rs` — the capability env
snapshots around argument lowering of `extern fn` calls, so a `&mut` out-param
borrow ends when the call ends. Sequential disjoint re-borrows of the same local
at later extern calls (the canonical retry/fallback out-param idiom) no longer
fail with `Aliasing violation: reference N already has Exclusive capability`.
Regression tests: `test_extern_out_param_*` in
`src/compiler_rust/compiler/src/hir/lower/tests/lifetime_tests.rs`.

## Why only the seed lane

`hir/capability.rs` runs only in the Rust seed (`SIMPLE_NATIVE_BUILD_RUST=1`
native-build). The pure-Simple stage2 compiler has no capability pass, and SPipe
specs execute on the pure-Simple compiler, so the RED/GREEN regression is a Rust
test; the checks below are the manual re-verification equivalent.

## 1. RED/GREEN unit level

```bash
cd src/compiler_rust
CC="$HOME/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe" \
CARGO_TARGET_DIR=$PWD/../../build/p3cache/outparam/cargo-target \
  cargo test --release -p simple-compiler extern_out_param -- --nocapture
```

Expected: 3 tests pass —
`test_extern_out_param_sequential_reborrow_allowed` (the doc's idiom),
`test_extern_out_param_two_mut_args_same_call_rejected` (one-call aliasing
still rejected), `test_extern_out_param_prior_borrow_binding_still_tracked`
(a borrow bound before the call still blocks re-borrow).

## 2. Stage-2-shaped probe (seed native-build lane)

Scratch build of the driver (do NOT touch `build/p3cache/fresh-seed/simple.exe`):

```bash
cd src/compiler_rust
CC="$HOME/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe" \
CARGO_TARGET_DIR=$PWD/../../build/p3cache/outparam/cargo-target \
  cargo build --release -p simple-driver
```

Retry-idiom probe (fails pre-fix with the capability error, must compile post-fix):

```bash
cd <repo root>
mkdir -p build/p3cache/outparam/tmp build/p3cache/outparam/hir-cache
# probe source: build/p3cache/outparam/probe/mut_out_param_retry_entry.spl
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_HIR_CACHE=0 \
SIMPLE_HIR_CACHE_DIR="$PWD/build/p3cache/outparam/hir-cache" \
TMPDIR="$PWD/build/p3cache/outparam/tmp" \
  ./build/p3cache/outparam/cargo-target/release/simple.exe native-build \
  --source build/p3cache/outparam/probe \
  --entry build/p3cache/outparam/probe/mut_out_param_retry_entry.spl \
  --entry-closure -o build/p3cache/outparam/probe-retry.exe
```

Expected post-fix: `compiled=1 ... failed=0`, link completes. Pre-fix signature:
`hir: Capability error: Aliasing violation: reference 2 already has Exclusive
capability, cannot acquire Exclusive`.

Module-level probe (the doc's Stage-2-shaped minimal entry):

```bash
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_HIR_CACHE=0 \
SIMPLE_HIR_CACHE_DIR="$PWD/build/p3cache/outparam/hir-cache" \
TMPDIR="$PWD/build/p3cache/outparam/tmp" \
  ./build/p3cache/outparam/cargo-target/release/simple.exe native-build \
  --source build/p3cache/outparam/probe --source src/lib --source src/compiler --source src/app \
  --entry build/p3cache/outparam/probe/stage2_shape_entry.spl \
  --entry-closure -o build/p3cache/outparam/probe.exe
```

Expected: `Build complete: 78 compiled, 0 cached, 0 failed` (the whole
`std.nogc_sync_mut.sffi.dynamic` closure compiles through the capability lane).

Full Stage-2 entry (closest to the doc's original abort; heavy, run on an idle
machine — concurrent CPU-heavy work trips per-file worker timeouts that surface
as unrelated `NOT_ATTEMPTED` admissions):

```bash
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_HIR_CACHE=0 \
SIMPLE_HIR_CACHE_DIR="$PWD/build/p3cache/outparam/hir-cache" \
TMPDIR="$PWD/build/p3cache/outparam/tmp" \
  ./build/p3cache/outparam/cargo-target/release/simple.exe native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry src/app/cli/bootstrap_main.spl --entry-closure \
  -o build/p3cache/outparam/stage2.exe
```

Expected: no `Capability error` / `Aliasing violation` in the failed-file list;
`failed=0`.
