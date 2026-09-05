# Engine2D factory returns a module-namespace dict under the test runner (match-arm binding shadowed by MODULE_GLOBALS)

- **ID:** `engine2d_factory_returns_dict_under_test_runner_2026-08-19`
- Status: OPEN (P1)
- **Found:** 2026-08-19
- Related: `module_named_like_its_class_shadows_it_inside_it_blocks_2026-08-04`
  (same root fact 1: importing one symbol registers the WHOLE module under its
  last-path-segment name), `spec_it_block_reads_stale_module_var_2026-08-04`
  (whose fix introduced the read path that makes this bite),
  `import_triggered_cross_module_symbol_misdispatch_2026-08-18` (sibling
  symbol-resolution class, different mechanism).

## Symptom

Under `bin/simple test`, `Engine2D.create_with_backend(10, 10, "cpu")` /
`create_with_backend_strict(...).unwrap()` returns a **dict** — either `{}` or
the backend_capability constants (`{ADRENO_PREFERRED_WORKGROUP: 64,
BACKEND_CPU: cpu, ...}`) — so every subsequent method call fails:

```
semantic: method `backend_name` not found on type `dict` (receiver value: {ADRENO_..., BACKEND_CPU: cpu, ...})
```

9 failures in `test/02_integration/rendering/vulkan_strict_spec.spl`, 2 in
`test/02_integration/rendering/engine2d_drawing_spec.spl`. The identical code
via `bin/simple run` works (`ok backend=cpu`). Import style is irrelevant:
`std.gpu.engine2d.engine` and `std.gc_async_mut.gpu.engine2d.engine` both fail
(verified); `cuda_strict_spec.spl` passes only because its assertions never
route through a match arm that binds the name `engine`.

## Minimal repro (verified 2026-08-19, seed of 01:32)

```spl
use std.spec.{describe, it, expect}
use std.gc_async_mut.gpu.engine2d.engine.{Engine2D}

describe "probe":
    it "arm binding named engine":
        match Engine2D.create_requested_backend(4, 4, "cpu"):
            Ok(engine):
                print(engine.backend_name())   # FAILS: receiver is the module dict
            Err(_):
                pass_do_nothing
    it "arm binding named eng":
        match Engine2D.create_requested_backend(4, 4, "cpu"):
            Ok(eng):
                print(eng.backend_name())      # PASSES
            Err(_):
                pass_do_nothing
```

The ONLY difference is the binding name `engine` — which is also the
last-path-segment of the imported module `...engine2d.engine`.

## Mechanism

Three facts combine (all interpreter lane, runner context only):

1. `use ....engine2d.engine.{Engine2D}` registers the whole module as a
   namespace dict under the bare name `engine` in the flat `MODULE_GLOBALS`
   (known behaviour, bug 2026-08-04). Under `run` the main module's imports do
   not land there, which is why standalone runs pass.
2. Match-arm pattern bindings are inserted with plain `env.insert` and are
   **never marked local** — `interpreter_control.rs` ~line 4849 ("Scope arm
   bindings to the arm body") pushes/restores shadows but calls neither
   `enter_block_local` nor `mark_local`, unlike `block_exec.rs:79` for block
   `let`s and `function_exec.rs:393 mark_nodes_locals` for top-level `Let`
   nodes (which does not recurse into match arms).
3. The identifier read path added for
   `spec_it_block_reads_stale_module_var_2026-08-04`
   (`interpreter/expr/literals.rs` ~300) prefers `MODULE_GLOBALS[name]` over
   the env value whenever `!env.is_local(name)` — so inside the arm body the
   bare read of `engine` returns the imported module's namespace dict instead
   of the freshly bound engine value.

`Engine2D.create_with_backend` itself contains `match created: Ok(engine):
return engine` (engine.spl:466ff), so the corruption happens inside the stdlib
factory: it returns the module dict to the spec.

## Impact

- Any match arm (or nested pattern) whose binding name equals ANY imported
  module's last path segment silently reads the module dict under the test
  runner. `engine`, `backend`, `color`, `compositor`, `mod` etc. are all common
  binding names AND common module basenames — a wide silent-corruption class.

## Fix proposal (Rust interpreter, not applied — files are mid-edit by another session)

Primary: in `src/compiler_rust/compiler/src/interpreter_control.rs`
(`exec_match_with_value`, ~4849), mark arm bindings block-local exactly like
`block_exec.rs` shadows: `env.enter_block_local(&name)` when inserting each
binding and `env.exit_block_local(&name)` in the restore loop (including the
error path). Then `env.is_local` is true inside the arm and literals.rs keeps
the binding. Extend the same to any other pattern-binding site that uses bare
`env.insert` (guard bindings, if-let, etc.).

Defensive hardening: in `interpreter/expr/literals.rs` ~300, never let the
`!is_local` MODULE_GLOBALS-preference return a module-NAMESPACE dict over an
existing env binding — namespace registrations are not "live module vars" and
should never win a read that has a bound env value.

Spec-side workaround (NOT applied — renaming every `engine` local would
normalize a compiler bug): rename match bindings named after imported module
basenames.

## Verification plan

- Failing-pre-fix repro spec above; plus neighbors: binding named `color`
  vs `use ...engine2d.color`, and a `for` / `if-let` pattern binding variant.
- After fix: `bin/simple test test/02_integration/rendering/engine2d_drawing_spec.spl`
  (2/2), `vulkan_strict_spec.spl`, `cuda_strict_spec.spl` stay green.
