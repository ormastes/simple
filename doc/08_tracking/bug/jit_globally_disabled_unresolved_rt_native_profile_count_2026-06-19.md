# JIT globally disabled: unresolved `rt_native_profile_count` forces interpreter fallback for ALL programs

- **ID:** jit_globally_disabled_unresolved_rt_native_profile_count_2026-06-19
- **Severity:** P1 (global performance regression — JIT off for every Simple program)
- **Found:** 2026-06-19, while pursuing within-arch perf optimization of the 8K scroll showcase.
- **Status:** FIXED 2026-06-19 (JIT restored + verified; see Resolution)

## Symptom

Every Simple program — including a trivial 1000-iteration loop — logs:

```
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile:
Module error: unresolved external symbol 'rt_native_profile_count' would NULL-jump
in JIT; deferring to interpreter
```

and runs in the (10–100× slower) interpreter. Reproduce:

```bash
printf 'fn main() -> i32:\n  var s = 0\n  var i = 0\n  while i < 1000:\n    s = s + i\n    i = i + 1\n  return 0\n' > /tmp/jit_probe.spl
bin/simple run /tmp/jit_probe.spl 2>&1 | grep -i jit
```

The trivial program references nothing profiling-related, yet JIT still defers.

## Root cause

`rt_native_profile_count` is registered as a JIT `RuntimeFuncSpec`
(`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1344`):

```rust
RuntimeFuncSpec::new("rt_native_profile_count", &[I64], &[]),  // name_ptr -> ()
```

but there is **no backing `extern "C" fn rt_native_profile_count` symbol** anywhere
in `src/compiler_rust/runtime/src/`. The codegen call site that would emit a call to
it is gated behind `SIMPLE_NATIVE_PROFILE_COUNTERS=1`
(`codegen/instr/body.rs:466`, `codegen/llvm/functions.rs:379`), so the *call* is
never emitted when instrumentation is off — but the *spec/import* is still presented
to the Cranelift JIT module, and the pre-finalize NULL-jump guard
(`codegen/jit.rs:89-103`) rejects any unresolved import, deferring the whole module
to the interpreter.

Net: a `RuntimeFuncSpec` with no linkable runtime symbol disables JIT for *all*
programs, not just instrumented ones. Introduced by in-flight native function-profile
counter work (see sibling docs `native_build_function_profile_counters_2026-06-19`,
`native_profile_counters_httpserver_crash_2026-06-19`).

## Impact

- JIT is off host-wide: all `bin/simple run` workloads are interpreter-bound.
- 8K software-render benchmarks cannot complete one full frame within the 10s example
  timeout in the interpreter, making within-arch render perf work unmeasurable until
  JIT is restored. JIT autovectorizes the per-pixel raster/blit loops; the interpreter
  dispatches per element.

## Fix options (verify against runtime before applying — author hypotheses)

1. **Minimal/safe:** add a no-op `#[no_mangle] pub extern "C" fn rt_native_profile_count(_name_ptr: i64) {}`
   (with the matching `#[cfg(not(feature=...))]` form if gated) to the runtime crate so
   the symbol resolves. JIT stops deferring; gated instrumentation still works when
   `SIMPLE_NATIVE_PROFILE_COUNTERS=1`. ~4 lines, no behavior change.
2. **Narrower:** only register the `rt_native_profile_count` `RuntimeFuncSpec` when
   `SIMPLE_NATIVE_PROFILE_COUNTERS=1`, so the import is absent (and the guard never
   sees it) in the default path.
3. **Guard-level:** have the JIT NULL-jump guard ignore specs that are declared but
   never referenced by the compiled module (only fail on *used* unresolved imports).

Any of these requires a Rust-seed change + `bin/simple` rebuild
(`cd src/compiler_rust && cargo build --release --bin simple --features simple-compiler/vulkan,simple-runtime/vulkan`).

## Resolution (2026-06-19, user-authorized "full fix")

Applied option 1, properly (real impl, not a no-op stub):

- Added `rt_native_profile_count` + `rt_native_profile_event` to the JIT
  runtime-symbol list `src/compiler_rust/common/src/runtime_symbols.rs` (so the
  build-generated symbol table registers them in the provider; `jit.rs`
  `jit_import_resolves` now finds them via `provider.get_symbol`).
- Added real implementations in new module
  `src/compiler_rust/runtime/src/native_profile.rs` (declared in `runtime/src/lib.rs`):
  a `parking_lot::Mutex<HashMap<name,count>>` with `atexit` TSV dump to
  `SIMPLE_NATIVE_PROFILE_OUT`, mirroring `runtime_native.c`'s format
  (`count\tfunction` + summary lines). Default (env unset) = cheap no-op. Two
  unit tests cover accumulation and null/empty-name handling.
- Rebuilt + redeployed `bin/release/x86_64-unknown-linux-gnu/simple`.

**Verified:** trivial program no longer logs the JIT fallback; JIT is active
(`SIMPLE_JIT_TRACE_ADDR=1` shows compiled functions). Measured impact on the 8K
scroll showcase full-repaint render (1280×800, 1.02M px/frame):
**interpreter 2,857 ms/frame (0.35 fps) → JIT 93 ms/frame (10.7 fps) = ~30.6× faster.**
Smoke: `bin/simple -c "print(1+1)"`=2, `bin/simple lint` exits 0 (no coredump).

**Remaining (separate, lower-priority) gap:** JIT/`run`-mode profiling does not
yet *emit* the counter call — `codegen/instr/body.rs:477` only emits when
`runtime_funcs` already contains `rt_native_profile_count`, which the JIT backend
does not populate for it (the feature's stated target is `native-build` AOT with
`--runtime-bundle core-c-bootstrap`, which already works). The runtime impl here
is correct and unit-tested, so wiring that emission later needs no runtime change.
Tracked as a codegen follow-up, not a blocker.
