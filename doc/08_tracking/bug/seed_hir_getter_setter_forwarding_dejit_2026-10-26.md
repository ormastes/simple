# Seed HIR: getter/setter forwarding dropped whole module to the interpreter

- **Severity:** P1 (perf / JIT coverage; with P0 sibling, wrong result)
- **Status:** fixed (this change)
- **Component:** `src/compiler_rust/compiler/src/hir/lower/expr/access.rs`, `hir/lower/stmt_lowering.rs`
- **Spec:** `test/01_unit/language/accessor_forwarding/accessor_forwarding_spec.spl` (JIT run uses `SIMPLE_JIT_STRICT=1`)

## Symptom

`t.celsius` / `t.hot` (getter forwarding) and `t.celsius = 40` (setter) failed
HIR lowering:

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'Temp' field 'celsius' (declared fields: _c)
[in build/fwd/getset_probe.spl]: whole module dropped to the interpreter
```

## Fix

- Field read: when no field resolves on the candidate struct, try
  `get_<f>` then `is_<f>` (interpreter order) and lower a real
  `receiver.get_<f>()` call so the method's declared return type is kept.
  (A first attempt built a `Dynamic` MethodCall typed ANY; the JIT then printed
  `class_get=0.000...004` and `class_is_after=nil` — recorded here because it is
  the trap.)
- Field write: `Lowerer::setter_forward_name` — a plain `=` to a non-field with a
  known `set_<f>` lowers to the statement `receiver.set_<f>(value)`.

Green: probe_setter under `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1` prints
all six CASE lines matching. Assignment to an undefined field with no setter
still fails closed in strict JIT (`unresolved external symbol 'rt_field_set'`)
and errors in the interpreter fallback — never a silent no-op.
