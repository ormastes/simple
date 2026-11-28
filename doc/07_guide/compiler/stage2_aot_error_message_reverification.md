# Seed / stage-2 re-verification: AOT compile error message survives in full

Recipe for re-checking
`doc/08_tracking/bug/stage2_aot_error_message_lost_invalid_heap_2026-09-06.md`
on the current tree and on every future stage-2 candidate. Do not edit the
bug record; run this recipe and append the outcome as a new lane addendum
elsewhere if a lane owns one.

## What the record claimed

A stage-2 AOT compile failure printed
`reason: AOT compile error in <unit>: <invalid-heap:0x...>` — the `Err`
payload text handle was destroyed crossing compiled frames on the
self-hosted binary, so the real backend reason was unrecoverable from the
build output.

## What is in the tree now (verified 2026-11-28, lane p3-sweep)

The payload loss does NOT reproduce on the current tree, on the seed lane,
end-to-end. Verified by forcing a real AOT object-stage failure through the
full `native-build` pipeline on a scratch seed build (see below): the unit
name, the `AOT compile error in <unit>: ...` wrapper, and the real backend
reason (clang's `unknown target CPU ...` rejection) all reach the operator
intact at every site:

- the raising-site bare prints from `_aot_compile_failure`
  (`src/compiler/80.driver/driver_aot_native_output.spl`),
- the ICE receipt (`build/ice/<pid>_<n>/ice_receipt.tsv`),
- the `[native-compile-failed] <unit>: ...` line,
- the end-of-build summary `reason:` block.

Why it is fixed: the raising site now prints the reason eagerly (independent
of the returned `Err`), every crossing re-binds the payload inside the arm
that reads it (`case Err(error): return Err(error)`, not forward-the-
composite), and empty/corrupt payloads are replaced with a named fallback
(`driver_native_nonempty_failure_detail`). Zero occurrences of
`<invalid-heap:`, `(none recorded`, or `diagnostic lost crossing` in the
forced-failure output; the bogus-CPU reason text appears six times.

Residual gap (NOT the recorded bug, not fixed here): when the native-build
worker subprocess fails, the parent relays the worker's stderr with the
middle bytes dropped once the stream exceeds the bounded limit
(`eprint_bounded` in `src/app/cli/native_build_main.spl`). The full stream
is spilled to a file and diagnostic lines are preserved, and the parent's
in-process re-run reprints the message, so nothing is unrecoverable — but
the worker's own head+tail excerpt alone can be missing the unit-name line.
File separately if it ever hides a message that the parent retry does not
reprint.

## The regression fence spec

`test/01_unit/compiler/backend/backend_aot_error_message_full_text_native_spec.spl`
forces the object-stage failure with `SIMPLE_NATIVE_CPU=<bogus>` (the object
tool rejects it with a real diagnostic) and asserts the full text survives.
GREEN on the current tree. RED on any binary whose AOT `Err` payload does
not survive the crossing (the 2026-09-06 stage-2 evidence shape:
`<invalid-heap:` present, reason text absent).

## Re-verify on the seed lane (this host, Windows GNU)

1. Build the seed driver into a scratch target dir (do NOT touch
   `build/p3cache/fresh-seed/simple.exe`):

   ```sh
   . scripts/setup/windows-gitbash-bootstrap-env.shs   # or set the env below by hand
   CC="$HOME/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe" \
   CARGO_TARGET_DIR=$PWD/build/p3cache/<lane>/cargo-target \
     cargo build --release -p simple-driver \
     --manifest-path src/compiler_rust/Cargo.toml \
     --target x86_64-pc-windows-gnullvm
   ```

   Required env (from `scripts/bootstrap/bootstrap-from-scratch.sh`'s GNU
   lane): `CARGO_TARGET_X86_64_PC_WINDOWS_GNULLVM_LINKER=<mingw>/bin/clang.exe`,
   `CC_x86_64_pc_windows_gnullvm=<mingw>/bin/clang.exe`,
   `AR_x86_64_pc_windows_gnullvm=<mingw>/bin/llvm-ar.exe`,
   `CFLAGS_x86_64_pc_windows_gnullvm=--target=x86_64-w64-windows-gnu`,
   `CARGO_TARGET_X86_64_PC_WINDOWS_GNULLVM_RUSTFLAGS="-Lnative=<mingw crt libdir> -C link-arg=--target=x86_64-w64-windows-gnu -C link-arg=-fuse-ld=lld"`.

2. Run the spec (run from the repository root; the fixture is admitted by
   repo-relative path):

   ```sh
   SIMPLE_BINARY=$PWD/build/p3cache/<lane>/cargo-target/x86_64-pc-windows-gnullvm/release/simple.exe \
   SIMPLE_HIR_CACHE_DIR=$PWD/build/p3cache/<lane>/hircache \
   TMPDIR=$PWD/build/p3cache/<lane>/tmp \
     "$SIMPLE_BINARY" test \
     test/01_unit/compiler/backend/backend_aot_error_message_full_text_native_spec.spl
   ```

   The spec prepares the child's environment on purpose, restoring it
   afterwards:
   - `SIMPLE_BINARY` is removed: left set, it steers native-build's producer
     binding onto the bootstrap route (compiling the compiler/runtime closure
     instead of the fixture's single unit) — a different lane from the one
     the record covers. Set-but-empty routes differently from unset, so the
     spec removes the variable rather than clearing it. A manual probe must
     not export `SIMPLE_BINARY` either.
   - `SIMPLE_EXECUTION_MODE` is pinned to `jit` for the child: the test
     runner executes specs on the interpreter and its mode leaks to children,
     which routes native-build through a worker subprocess with a different
     summary shape. The record is about a COMPILED lane, so the probe pins
     the compiled (jit) lane explicitly — the same class as the stage-2
     binary under test.
   - `SIMPLE_MCDC_MODE`/`SIMPLE_MCDC_INCLUDE`/`SIMPLE_MCDC_EXCLUDE` are
     removed for the child: the runner collects MC/DC coverage for the spec
     run, and those settings leak to children — entry-closure builds then
     inject the probe runtime modules (11 units instead of the fixture's
     single unit) and the MIR shard lane dies before the outcome summary.

3. On a contended host (other build lanes running), the build admission may
   refuse with `SIMPLE_BUILD_MEMORY_RESERVE_BYTES`; either wait or lower it
   for the probe run, e.g. `SIMPLE_BUILD_MEMORY_RESERVE_BYTES=4294967296`.
   If the LLVM tools are not on PATH, point
   `SIMPLE_LLVM_MINGW_ROOT=<llvm-mingw prefix>` at the toolchain so the
   object tool resolves.

## Re-verify on a stage-2 candidate

Run step 2 with `SIMPLE_BINARY=<stage-2 candidate>` after a bootstrap. The
spec must be GREEN; RED means the payload-corruption regressed in the
self-hosted lane and the record reopens.
