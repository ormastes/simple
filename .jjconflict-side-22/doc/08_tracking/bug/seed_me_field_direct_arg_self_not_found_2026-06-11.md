# Seed interpreter: `me.field` as direct arg to a nested `me fn` call → `self` not found

- **Status:** fixed in seed — pending redeploy (2026-06-11)
- **Found:** 2026-06-11 while fixing
  `dbfs_checkpoint_facade_spec_self_not_found_2026-06-11.md`
- **Severity:** medium — silent class of interpreter-mode failures; the error
  message (`semantic: variable 'self' not found`) points at the callee, not
  the offending argument expression.

## Minimal repro

```
# Previously failed in interpreter mode (now fixed):
me fn query(q: AttrQuery) -> AttrQueryResult:
    ids = me._query_index(me.size_index, q.op)   # me.field as direct arg

# Workaround (now reverted):
me fn query(q: AttrQuery) -> AttrQueryResult:
    var idx_copy = me.size_index
    ids = me._query_index(idx_copy, q.op)        # copy to local first
```

## Root Cause

`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` line 375
(`handle_method_call_with_self_update`, Identifier receiver fast path):

```rust
if let Some(Value::Object { class, fields }) = env.remove(obj_name) {
    match find_and_exec_method_with_self_owned(method, args, &class, fields, env, ...)
```

`env.remove(obj_name)` removes the caller's `self` from env BEFORE `args` are
evaluated. `find_and_exec_method_with_self_owned → exec_function_with_self_return`
calls `bind_args(args, outer_env=env)` — but `env` no longer contains `self`, so
any arg expression `me.field` (which lowers to `self.field`) fails with
`variable 'self' not found`.

## Fix (2026-06-11)

`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`:
After `env.remove(obj_name)`, immediately re-insert a clone of the object into
`env` so that arg expressions containing `self` can still resolve during
`bind_args`. This costs one extra Arc refcount bump for the duration of the call
(minor perf trade-off, acceptable).

`src/compiler_rust/compiler/src/interpreter_method/mod.rs`:
Also fixed the two typed-dict dispatch paths (lines ~146, ~157) that similarly
mutated `outer_env` with `self=` before calling `exec_function(..., None)` —
changed to pass `self_fields` via `self_ctx` (`Some((type_name, &self_fields))`).

## Regression test

`interpreter::interpreter_method::tests::me_field_as_direct_arg_to_me_fn_does_not_error`
in `src/compiler_rust/compiler/src/interpreter_method/mod.rs` — passes green.

## Workaround reverted

`src/lib/nogc_sync_mut/db/dbfs_engine/attr_index.spl` — `query` and
`_remove_from_field_index` now pass `me.<field>` directly again.

## Verification (fresh binary: src/compiler_rust/target/release/simple)

- repro `/tmp/me_field_repro.spl` → prints `10` ✓
- `dbfs_checkpoint_attr_facade_spec` → 1 passed ✓
- `pager_wal_gate_spec` → 13 passed ✓
- `dbfs_engine_checkpoint_spec`, `dbfs_engine_checkpoint_ring_spec` → 4 passed ✓

## Notes

- Pending redeploy: orchestrator handles deployment with smoke gates.
- The plain-`fn self.` strictness (mutable methods must be `me fn`) is
  by-design and unrelated to this bug.
