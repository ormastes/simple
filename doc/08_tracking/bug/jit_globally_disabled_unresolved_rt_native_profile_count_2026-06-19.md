# JIT globally disabled: unresolved `rt_native_profile_count` forces interpreter fallback for ALL programs

- **ID:** jit_globally_disabled_unresolved_rt_native_profile_count_2026-06-19
- **Severity:** P1 (global performance regression — JIT off for every Simple program)
- **Found:** 2026-06-19, while pursuing within-arch perf optimization of the 8K scroll showcase.
- **Status:** OPEN

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
Per project rule "fix Simple source first; don't modify Rust seed unless explicitly
asked," this is recorded rather than applied unilaterally.
