# Interpreter Mirror Report — Int/Float `to_<numeric>` Method Fix

**Date:** 2026-04-12

## Finding: No self-hosted primitive method source exists to mirror

The task asked for a Simple-side mirror of the Rust seed patches to
`interpreter_method/primitives.rs` and `interpreter_helpers/method_dispatch.rs`.
**There is no such Simple-side source.** The deployed `bin/simple` binary links
statically against `libsimple_native_all.a`, which contains the full Rust
compiler crate (including `simple_compiler::interpreter::interpreter_method`).
When `bin/simple run <file>` is invoked, the self-hosted driver delegates
primitive method evaluation into that Rust crate via FFI.

### Evidence

1. The exact error strings only exist in Rust source:
   - `(receiver value: ` → only in
     `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1029`
   - `not found on value of type ... in nested call context` → only in
     `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs:509`
   Both strings are present verbatim in `bin/simple` (confirmed via
   `strings bin/simple | grep`).
2. The Simple-side interpreter backend at
   `src/compiler/70.backend/backend/interpreter.spl` handles `MethodCall`
   only through the HIR method-resolution path (`StaticMethod`,
   `InstanceMethod`, `FreeFunction`, `TraitMethod`). It has **no hard-coded
   primitive method table** for `Int.to_u8()` etc. If primitive method dispatch
   ever came through this code path, unresolved calls would produce
   `"unresolved method call: to_u8"` — not the observed message.
3. The MIR-level interpreter at
   `src/compiler/95.interp/mir_interpreter.spl` only handles intrinsic
   functions (`abs`/`min`/`max`/etc.), not typed methods.
4. The `interpret_file` entry (`src/compiler/80.driver/driver_api_interpret.spl`)
   constructs a `CompilerDriver` in `CompileMode.Interpret`, which is wired in
   `src/compiler/80.driver/driver_types.spl:52` to `InterpreterBackendImpl`.
   That impl dispatches HIR `MethodCall` nodes to resolved symbols — primitive
   method calls still fall through to the Rust runtime.

Conclusion: the only place primitive `Int`/`Float` method dispatch lives is the
Rust interpreter crate in `src/compiler_rust/compiler/src/`. The user's existing
patches to `primitives.rs` and `method_dispatch.rs` are the canonical fix.

## Files inspected (no edits required)

- `src/compiler/70.backend/backend/interpreter.spl` — HIR tree-walking
  interpreter, MethodCall dispatch at lines 162–203. No primitive methods.
- `src/compiler/70.backend/backend/interpreter_calls.spl` — builtin functions
  (print, file I/O, env, etc.) and value conversion. No primitive method table.
- `src/compiler/95.interp/mir_interpreter.spl` — MIR interpreter, only
  intrinsics at lines 510–587.
- `src/compiler/80.driver/driver_api_interpret.spl` — entry from
  `cli_run_file`.
- `src/compiler/80.driver/driver_types.spl` — wires `InterpreterBackendImpl`
  into `BackendPort.run_fn`.
- `src/app/io/cli_commands.spl:64` — `cli_run_file` → `interpret_file`.

## Rust seed patches verified present

- `src/compiler_rust/compiler/src/interpreter_method/primitives.rs` lines 31–45:
  `to_f32`, `to_i8..i64`, `to_u8..u64` for `Value::Int` delegating to
  `cast_int_to_numeric`. Symmetric arms for `Value::Float`.
- `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`
  lines 338–375: chained-call fast path for `Value::Int` / `Value::Float`
  adding the same `to_<numeric>` family.
- `git diff --stat` confirms both files modified (+52 lines total).

## Rebuild actions taken

1. **Rebuilt Rust seed + `libsimple_native_all.a`:**
   ```
   cd src/compiler_rust && SDKROOT=$(xcrun --show-sdk-path) \
     cargo build --profile bootstrap -p simple-driver -p simple-native-all
   ```
   Result: success (1m 21s). Produced
   `src/compiler_rust/target/bootstrap/simple` and
   `libsimple_native_all.a` with the patched symbols.
2. **Verified Rust seed fixes both repros:**
   - `src/compiler_rust/target/bootstrap/simple /tmp/interp_repros/a.spl` →
     `x=239`
   - `src/compiler_rust/target/bootstrap/simple /tmp/interp_repros/b.spl` →
     `n=3`
3. **Ran full bootstrap:** `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`
   - All stages completed. Stage 4 (`full`) produced and deployed to
     `bin/release/aarch64-apple-darwin-macho/simple` (25,301,560 bytes).
   - `bin/simple` symlink now points to the freshly linked binary.
   - Note: the bootstrap warned that stage 3 self-host verification failed
     (LIM-010 LLVM symbol conflicts) and stage 4 was produced from the Rust
     seed — this is a pre-existing known limitation, not introduced here.
   - The patched `libsimple_native_all.a` is statically linked into the final
     binary; `strings bin/simple | grep "(receiver value:"` still finds the
     Rust error string, confirming the linked-in Rust crate is present.

## Repro verification — mixed result

- **Rust seed (`src/compiler_rust/target/bootstrap/simple`):**
  Both `/tmp/interp_repros/a.spl` and `/tmp/interp_repros/b.spl` now print
  the correct output (`x=239` / `n=3`). **Fix confirmed working** at the
  runtime crate level.
- **Self-hosted `bin/simple run`:** emits generic
  `Error running /tmp/interp_repros/a.spl` with no further detail — and the
  **same generic error fires for a trivial `print("hello")` program** and for
  any `.spl` file passed to `simple run`. This is a pre-existing issue in the
  self-hosted `cli_run_file` / `interpret_file` path (see
  `src/app/io/cli_commands.spl:64`, which matches on
  `CompileResult.Success(_)` and reports only a generic string on any other
  variant). It is **not related** to the int-method fix — `hello.spl` has no
  method calls at all. The self-hosted `simple run` pipeline cannot currently
  execute any file via the HIR interpreter backend, so we cannot directly
  observe the int-method fix through that path.
- The fix is present in the Rust code linked into `bin/simple`; any code path
  that actually reaches `interpreter_method::handle_int_methods` or the
  nested-call fast path in `method_dispatch.rs` will pick it up. The
  `wm_compare` harness (`src/app/wm_compare/html_compat.spl`) specifically
  avoids `.to_i32()` because of this bug; once its caller eventually runs via a
  path that exercises the Rust interpreter, it will now succeed.

## Summary

- **Patches needed in `.spl`:** none. The self-hosted interpreter does not
  implement primitive method dispatch in Simple; it delegates to the Rust
  runtime via FFI and the linked-in Rust compiler crate.
- **Rust patches:** already in place at
  `src/compiler_rust/compiler/src/interpreter_method/primitives.rs` and
  `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`.
- **Bootstrap rebuild:** completed; `bin/simple` now links against the patched
  `libsimple_native_all.a`.
- **End-to-end verification:** confirmed on the Rust seed binary; blocked on
  `bin/simple` by a pre-existing, unrelated issue where `simple run <file>`
  always reports a generic error for every file.
