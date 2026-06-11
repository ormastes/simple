# Bug: out-of-bounds array read SIGSEGVs in cranelift binaries (interpreter returns 0)

- **Date:** 2026-06-11
- **Status:** open (guards added at the bridge call sites that crashed)
- **Severity:** high — semantics diverge between interpreter and compiled code

## Symptom

```spl
fn main():
    val a: [i64] = []
    val x = a[3]
    print("OOB val {x}")
```

- **Interpreter (Rust seed):** prints `OOB val 0` (graceful default).
- **Cranelift-compiled:** SIGSEGV (verified: native-build `tmp/site12/oob.spl`,
  run in docker → rc=139).

## Impact found

`decl_is_async[idx]` in `convert_decl_method_fn`
(src/compiler/10.frontend/flat_ast_bridge_part1.spl) raw-indexed a module-level
array that the lean-parser flow never populates (decl_fn only writes the
ASYNC value to the env transport). In the stage4 self-hosted binary this was
one of the two crashes behind the 12th-site cluster. Fixed by routing through
`decl_get_is_async` / new `decl_get_is_gpu_kernel` with nil+length guards
(src/compiler/10.frontend/core/ast_part1.spl).

## Fix direction

Cranelift array-index lowering should match interpreter semantics: bounds-check
and produce the default value (or a runtime panic with a message) instead of
dereferencing past the allocation. Same family as the earlier rt_tuple_get /
rt_array_get fallback fixes (site 8).
