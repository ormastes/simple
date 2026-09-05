# Interp: `var` local becomes "const" after a `me`-method call, under the sspec runner

- **Date:** 2026-07-21
- **Status:** FIXED + VERIFIED (same day; root cause was neither `me`-methods nor sspec — see below)
- **Area:** Rust seed interpreter — unframed STATIC method dispatch
  (`interpreter_method/special/objects.rs::handle_constructor_methods`)
- **Severity:** medium (spurious semantic error; breaks valid code in specs)

## ROOT CAUSE (supersedes the initial analysis below)

Traced with the new env-gated `SIMPLE_CONST_TRACE=<name>` instrumentation
(kept in `interpreter_state.rs`): `CONST_NAMES` is a process-global
thread-local set scoped per call frame by `execute_function_body`
(mem::take at entry, restore at exit). But STATIC method calls
(`Type.method(...)`) dispatch through `handle_constructor_methods`, which ran
the body via `exec_block_fn` directly — NO frame swap. Any `val x` in a
static body therefore leaked 'x' into the CALLER's const set, and the
caller's later `x = ...` on its own `var x` died with "cannot assign to
const 'x'". In the original repro the poisoner was
`BackendProbeResult.create`'s `val ok` (backend_probe.spl:54), reached via
`Engine2D.create_with_backend_strict` → the `me`-method and sspec context
were incidental. Same JIT-vs-interp artifact as the sibling bug: plain-main
runs JIT'd and never touched CONST_NAMES; specs fall back to the
interpreter. 14-line pure repro: cross-module static with `val flag` +
caller `var flag`, run with `SIMPLE_EXECUTION_MODE=interpreter`.

**Fix:** `handle_constructor_methods` static-body execution now performs the
same CONST_NAMES/IMMUTABLE_VARS take/always-restore as
`execute_function_body`. Regression gate:
`test/01_unit/compiler/interp/static_method_const_frame_spec.spl`.

## Symptom

`semantic: cannot assign to const 'ok'` on a plain `var` local, but only when
ALL of these hold:

1. the function runs under the sspec runner (called from an `it` block —
   directly in `fn main` the same code passes),
2. a class instance obtained via `Result.unwrap()` receives a `me`-method
   call before the reassignment.

## Minimal repro (18 lines)

```simple
use std.spec.*
use std.gpu.engine2d.engine.{Engine2D}
use std.gpu.engine2d.color.{rgb}

fn strict_like(name: text) -> bool:
    var ok = false
    val created = Engine2D.create_with_backend_strict(16, 16, name)
    if created.is_ok():
        var eng = created.unwrap()
        eng.clear(rgb(0, 0, 0))
        ok = true            # <- semantic: cannot assign to const 'ok'
        eng.shutdown()
    ok

describe "const repro":
    it "engine unwrap + me-method + var reassign":
        assert_true(strict_like("cpu"))
```

Removing the `eng.clear(...)` call (or running `strict_like` from `fn main`
instead of an `it`) makes the reassignment legal again. Simple var-reassign
in helpers called from `it` blocks WITHOUT a preceding `me`-method call works
fine (verified).

## Suspected mechanism

The gdb frame family from the sibling vulkan investigation shows method calls
route through `interpreter_helpers::patterns::handle_method_call_with_self_update`;
the self-writeback appears to re-snapshot enclosing locals with a const
binding when the call happens inside the spec-runner's closure evaluation.
Related context-sensitive interp bug found the same day:
[[interp_empty_event_array_result_match_erasure_2026-07-21]] (extern empty
array degrades to i64 0 only under the sspec runner).

## Workaround (applied)

`test/02_integration/gpu/engine2d_backend_matrix_spec.spl` helpers
restructured to `val`-combination style (compute branch results as `val`s,
return boolean expressions; no reassignment after `me`-method calls).

## Binary identity

Seed rebuilt from WC 2026-07-21 (`cargo build --profile bootstrap`,
`src/compiler_rust/target/bootstrap/simple`), deployed at
`bin/release/x86_64-unknown-linux-gnu/simple` with seed warning banner.
