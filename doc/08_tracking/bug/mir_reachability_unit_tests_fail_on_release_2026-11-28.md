# Two `mir::reachability` unit tests fail on release/1.0.0

- Date: 2026-11-28
- Status: verification-pending
- Area: `src/compiler_rust/compiler/src/mir/reachability.rs` (seed JIT reachability)
- Found by: the #12295 test run. Reproduced on `322e8d8bca1`, the commit before #12295, so #12295 did not cause it.

## Repro

```
cd src/compiler_rust
cargo test --release -p simple-compiler --lib mir::reachability
# test result: FAILED. 10 passed; 2 failed
```

1. `every_function_sharing_a_probed_tail_is_kept` (reachability.rs:501)
   `Type.foo dropped: {"a__foo", "b__foo", "main"}`.
   A bare call `foo` no longer keeps `Type.foo`. The module doc's
   soundness rule says every function sharing a probed tail stays, so that
   removing one never makes another unique and rebinds a call. Either that
   rule is violated, which risks a silent rebind in the JIT, or the rule was
   deliberately narrowed for methods and the test and doc are stale.
2. `flattened_private_names_never_wake_unrelated_same_named_methods`
   (reachability.rs:725): the keep set is
   `{"__spl_flat_win_spl_deadbeef__create", "__spl_flat_pty_spl_cafe__read", "main"}`.
   The test also expects `rt_file_exists`, which is the tail of the called
   `__spl_flat_io_spl_1234__rt_file_exists`, to be in the keep set.

The last logic change to the file is `74454b58b2f` (2026-11-21, Wave H4).
That is likely where the `call_name_keys` / flatten-owner exact-key change
happened.

## Cause

Both failures come from `74454b58b2f`. That commit added test 2 already failing, and its change broke test 1.

1. That commit deliberately stopped a bare name from keeping `Type.foo`: method definitions now keep their `Type` owner in their keys. Codegen agrees, so dropping `Type.foo` is sound:
   - `compile_call` looks a direct call up only by its exact name, in `func_ids`, `use_map` and `import_map`.
   - `FuncIdTable::resolve_unique_module_qualified` files `Type.foo` under the tail `Type_dot_foo`, so a probe for `foo` never reaches it.
   - Only erased-receiver method calls rebind a bare name to `T.foo`: the `use_map` / `import_map` scans in `compile_method_call_static`. Reachability matches that, because `MethodCallStatic` / `BuiltinMethod` set `allow_bare` and wake `methods_by_bare_name`.

   The test and the module doc were stale.
2. The check `keep.contains("rt_file_exists")` could never pass. The keep set only holds *defined* functions, and the fixture defined no `rt_file_exists`.

## Fix

The fix changes no code, only tests and docs:
- Test 1 now asserts that a direct `Call foo` keeps `a__foo` and `b__foo` and drops `Type.foo`. It then adds a `MethodCallStatic foo` and asserts that `Type.foo` is kept.
- Test 2's fixture now defines the local `rt_file_exists` body that the flattened call must reach.
- The module doc's soundness rule now describes the exception for method definitions.
