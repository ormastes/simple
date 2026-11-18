# `xs.copy()` on a local array dispatches to a foreign static method named `copy`

- **Date:** 2026-11-19
- **Status:** fixed in source (MIR-level proof on the seed interpreter; native proof
  needs a new Stage 2); the Stage 3 crash site keeps a source workaround until then
- **Lane:** Stage 2 (seed-built, cranelift) -> Stage 3 -> Stage 3 self-build, aarch64 Linux
- **Source pin:** release/1.0.0 `9f89b7d0b55`
- **Family:** `stage3_selfbuild_raw_text_strict_extern_2026-11-18.md` (same symptom
  line, different root)

## Symptom

Stage 3 (built by Stage 2) prints exactly once, as `surface_build` starts:

```
[simple-runtime][error] rejected invalid array handle before dereference; probable
compiler/FFI ABI mismatch (value_bits=0x0000ab5f47e4af51)
```

and the build continues. Stage 2 on identical input prints nothing. It needs `--source`
roots (the coordinator route that parses `__init__.spl` visibility manifests); a plain
`native-build main.spl --entry-closure` never reaches the site. An 88-file closure in a
scratch git repository reproduces it in about 80 s.

## Root cause

`src/compiler/80.driver/driver_source_parse_selected.spl`,
`parse_visibility_manifest_policy_v1`:

```
val friend_modules: [text] = module.friends
policy.friend_modules = friend_modules.copy()      # same for internal_exports
```

A method call on a function-local has no `MethodResolution` on the native lane, so it
reaches the `Unresolved` arm of `lower_method_call_by_resolution_v1`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`). That arm recovers a
type-valued receiver whose name was lost with `lookup_unique_static_method(method)`: if
exactly one static function in the symbol table has that leaf name, the call becomes a
call of that static. The guard only excluded proven scalars, known record owners and
call-result receivers. A local array is none of those, and the only static leaf named
`copy` visible there is `MirOperand.copy(local: LocalId)`.

Stage 2 therefore lowered both lines to a zero-argument call of `MirOperand.copy` (the
receiver is dropped; the callee reads whatever is in the argument register) and stored
the returned `MirOperand` record in two `[text]` fields. Measured in the Stage 3 binary:
the only two non-MIR callers of `compiler.mir.mir_instruction_support.MirOperand.copy`
are these two lines, and at `rt_transient_heap_promote(policy)` both fields hold an
unregistered 3-word record instead of an array. The first reader,
`surface_manifest_policy_copy_v1` (`policy.friend_modules.copy()` ->
`rt_array_len`), trips the runtime guard, which reports once.

Effect before the guard message: every manifest policy's `friend_modules` and
`internal_exports` are garbage, and the guarded read yields length 0, so the surface copy is empty — friend and
internal-export visibility facts are silently dropped in a Stage 3 build.

Within one module the mismatch is loud (cranelift verifier: `mismatched argument count
... got 0, expected 1`); across modules nothing checks the arity, which is why the
self-build got a binary.

## Fix

`method_receiver_roots_at_bound_local_v1`: a receiver that is a function-local binding,
or a field chain rooted at one, is a runtime value and can never be a lost type name, so
the unique-static-leaf recovery is skipped for it. The check runs before the leaf scan,
so those calls also skip the walk over every exact symbol. The call then falls through
to the receiver-typed builtins (`arr.copy()` -> counted array copy).

- Spec: `test/01_unit/compiler/mir/array_copy_unique_static_leaf_spec.spl` — 2 of 6
  passed with the guard removed, 6 of 6 with it (seed `d322f63d44f9`, the seed that
  built the pinned Stage 2). `chained_named_receiver_owner_spec.spl` is 3 of 4 both
  before and after (its one failure is an unrelated HIR owner-facts error).
- Fixture: `test/fixtures/native_array_copy_unique_static_leaf/main.spl` — seed
  interpreter prints `2 a 2 b 3 2 b 1 x no 7`; Stage 2 `9f89b7d0b55` fails to build it
  (`unresolved method call: len ... owner=main.Op`, or the verifier arity error for the
  single-function shapes).
- `@workaround bug=stage3_array_copy_unique_static_leaf_2026-11-19` at the driver site:
  explicit copy loops instead of `.copy()`. The same shape (field of a match-bound
  record, loop + push, field store) was built with Stage 2 `9f89b7d0b55` and matches the
  seed interpreter.

## Not proven

- The lowering fix has no native proof: that needs a Stage 2 built from it.
- The driver workaround was checked on Stage 2 only as a reduced fixture, not by
  rebuilding Stage 3 and re-running the self-build.
- Receivers that are neither locals nor field chains of locals (module-level values,
  index expressions) still reach the unique-static-leaf recovery.
- Other static leaves that collide with builtin method names were not audited; the
  Stage 3 binary was only scanned for callers of `MirOperand.copy`.

## 2026-11-19 follow-up: `args.ptr()` in `codegen.spl` bound to `MirType.ptr`

With the guard in place, Phase 3 (Stage 2 from `41efdc0e7ea`) and the full-CLI build
both stop at `unresolved method call: ptr ... at src/compiler/70.backend/codegen.spl:688:42`,
`CraneliftCodegenState.call_function`: `cranelift_call_function_ptr(ptr, args.ptr(), args.len())`
with `args: [i64]`. Arrays have no `ptr()` builtin (only text does, via `rt_string_data`).

Old binding: `lookup_unique_static_method("ptr")` found the only static leaf named `ptr`
in the source tree, `static fn ptr(pointee: MirType, mutable: bool) -> MirType`
(`src/compiler/50.mir/mir_types.spl:253`; `MirType` is imported by `codegen.spl`). The
call was a zero-argument call of a two-parameter static, so `args_ptr` was a `MirType`
record (or garbage), never the array's data. It did no visible harm only because
`rt_cranelift_call_function_ptr` ignores its arguments: the Rust provider transmutes
the pointer to `extern "C" fn() -> i64`, and the C bootstrap stub traps.

Fix: `call_function` is zero-argument only. It refuses a non-empty `args` with a
codegen error and calls `cranelift_call_function_ptr(ptr, 0, 0)`, as
`cranelift_codegen_adapter.spl` already does. `rt_array_data_ptr` was rejected: a
`[i64]` buffer holds tagged runtime slots (`rt_value_int` stores `v << 3`, C callers
run `rv_to_int` on each element), not raw words. No caller passes arguments.

Also fixed: `get_function_ptr` passed `(module, name.ptr(), name.len())` to the
two-parameter wrapper `cranelift_get_function_ptr(module: i64, name: text)`. It now
passes `(module, name)`.

Sweep: in both build logs, `codegen.spl:688` is the only unresolved method call. A
static scan of `.ptr()` on receivers declared as arrays finds one more site,
`src/lib/nogc_async_mut/game3d/game_loop.spl:100` (`buf.ptr()` on `[0; size]`,
wasm-only, outside both closures). It is not fixed here.
