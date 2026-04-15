# Resume Doc — self.field.method() Resolution Bug

**Created:** 2026-04-14  
**Agent:** SFM  
**Deferred because:** VT4 is active and owns `hir/**` and `mir/**` territory.  
**Dispatch after:** VT4 completes (watch `jj st` — dirty files cleared from mir/lower/).

---

## Bug Summary

The seed compiler incorrectly resolves `self.field.method()` (and the general
pattern `expr.field.method(args)`). Instead of dispatching to the method on
the *field's declared type*, it either:

1. **Returns TypeId::ANY** for the receiver, so `lookup_method_return_type`
   cannot find the method — silent mis-codegen.
2. **Generates a recursive self-call** at MIR/Cranelift level: `engine.draw_rect_filled(...)`
   lowers to a call back into `Engine2D.draw_rect_filled` (the enclosing method),
   causing infinite recursion / stack overflow at runtime.

Phase-4 report STOP section documents the observable symptom: drawing had to be
bypassed via `rt_gui_fill4` direct MMIO from C to avoid the bug.

---

## Exact Repro

```
test/unit/compiler/semantic/self_field_method_resolution_spec.spl
```

Minimal SPL:
```spl
dataclass Inner:
  var value: i32
  fn foo() -> i32:
    return self.value

dataclass Outer:
  var inner: Inner
  fn trigger() -> i32:
    return self.inner.foo()   // <-- BREAKS HERE
```

Expected: `outer_val.trigger()` returns the `inner.value`.  
Actual: Either wrong return value (ANY fallback) or infinite recursion.

---

## Error Observed at Runtime

No compile-time error. At runtime, one of:
- `[WARN] unresolved fn: <method_name>` printed, then NIL/zero returned.
- Stack overflow / silent hang due to recursive self-call in Cranelift codegen.

The `[WARN] unresolved fn: addr` pattern from phase4_report.md is the same
root cause applied to `fb_info.addr.addr` — field-access receiver typed as ANY.

---

## Root Cause — Two-Layer Issue

### Layer 1 — HIR: `access.rs` CannotInferFieldType fallback

File: `src/compiler_rust/compiler/src/hir/lower/expr/access.rs`  
Lines: ~140–151

When `get_field_info(recv_hir.ty, field)` returns `CannotInferFieldType`,
`lower_field_access` falls through to:

```rust
Ok(HirExpr {
    kind: HirExprKind::MethodCall {
        receiver: recv_hir,
        method: field.to_string(),
        args: vec![],
        dispatch: DispatchMode::Dynamic,
    },
    ty: TypeId::ANY,   // <-- loses the field's declared type
})
```

The `ty: TypeId::ANY` means when `lower_method_call` in `mod.rs` later sees this
node as the receiver of another call (e.g., `self.inner.foo()` → receiver is the
`self.inner` FieldAccess node), `receiver_hir.ty` is `ANY`, so
`lookup_method_return_type` returns `ANY` and method name mangling is guesswork.

### Layer 2 — MIR/Cranelift: method name mangling on MethodCallStatic

File: `src/compiler_rust/compiler/src/mir/lower/lowering_expr.rs` (VT4 territory)

When `MethodCall` is lowered to `MethodCallStatic`, the `func_name` is built
by mangling `ReceiverType_dot_method`. If the receiver type is ANY (or wrong),
the mangler may produce the same mangled name as the *enclosing* function,
causing the Cranelift backend to emit a call to itself.

---

## Proposed Fix (patch-level detail)

### Fix A — HIR layer (preferred entry point, safer)

**File:** `src/compiler_rust/compiler/src/hir/lower/expr/access.rs`

In `lower_field_access`, when `get_field_info` returns `CannotInferFieldType`,
before falling back to a MethodCall stub, attempt a second lookup using the
*receiver's inferred struct type name*:

```rust
Err(LowerError::CannotInferFieldType { .. }) => {
    // NEW: try to resolve field type via struct name lookup
    if let Some(field_ty) = self.try_resolve_field_type_by_name(recv_hir.ty, field) {
        return Ok(HirExpr {
            kind: HirExprKind::FieldAccess {
                receiver: recv_hir,
                field_index: 0, // or look up actual index
            },
            ty: field_ty,  // <-- preserve real type, not ANY
        });
    }
    // existing fallback ...
    Ok(HirExpr {
        kind: HirExprKind::MethodCall { ... },
        ty: TypeId::ANY,
    })
}
```

Add helper `try_resolve_field_type_by_name(&self, recv_ty: TypeId, field: &str) -> Option<TypeId>`
that walks `self.module.types.get(recv_ty)` → `HirType::Struct { fields, .. }` →
finds the field by name → returns its `TypeId`.

### Fix B — Fallback: ensure global_struct_defs is populated for all structs

The existing `populate_global_struct_defs` flag in `native_project/mod.rs` limits
the fix to single-field wrapper structs. Extend the filter to include any struct
whose fields are all resolvable (not just `len() == 1`). This was conservative
due to the BeDomNode regression — but a more targeted exclusion list may be
safer than the blanket `len() == 1` gate.

**File:** `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs`  
Lines: the `populate_global_struct_defs` filter block.

---

## Regression Coverage

After fix, run:
```bash
bin/simple test test/unit/compiler/semantic/self_field_method_resolution_spec.spl
```

Also verify no regressions in:
- `test/baselines/wm_compare/engine2d_in_qemu/serial.log`
- BeDomNode-related tests (the cf800979c6 regression guard)

---

## Files to Edit (AFTER VT4 completes)

| File | Action | Territory |
|------|---------|-----------|
| `src/compiler_rust/compiler/src/hir/lower/expr/access.rs` | Add `try_resolve_field_type_by_name` + use in fallback branch | HIR (VT4) |
| `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs` | Extend struct filter | pipeline (check if VT4 dirty) |

**DO NOT TOUCH** `mir/lower/lowering_expr.rs` — VT4 owns it.
Fix Layer 1 (HIR) should be sufficient; Layer 2 is a consequence of Layer 1's
bad type info flowing downstream.

---

## Suggested Commit Message

```
fix(compiler): resolve self.field.method() dispatch via field type preservation

When get_field_info returns CannotInferFieldType, preserve the struct field's
declared TypeId instead of falling back to ANY. Prevents downstream MIR mangler
from generating recursive self-calls on field-delegated method invocations.

Fixes: Engine2D.draw_rect_filled() infinite-recursion (phase4 STOP marker)
```
