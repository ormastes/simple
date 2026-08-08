# HIR lowering: cannot infer bool field type on imported struct (falls back to interpreter)

- **Date:** 2026-07-03
- **Severity:** P2 (perf — JIT lost, program still runs via interpreter fallback)
- **Repro:** `bin/simple examples/12_business/simple_erp/src/business_suite.spl`
- **Error:** `[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unsupported feature: cannot infer field type while lowering session_valid: struct 'Session' field 'active'`

## Details

`Session` is declared in `examples/12_business/simple_erp/src/framework/guarded.spl`:

```
struct Session:
    val token: text
    val user_id: i64
    val tenant_id: text
    val active: bool
```

`session_valid` reads `session.active` (a `bool` field) on the imported struct.
Interpreter handles it fine; HIR lowering cannot infer the field type when the
struct crosses a module boundary (`use framework.guarded.{...}`), so the whole
run drops to the interpreter. The same pattern with `i64`/`text` fields lowers
without complaint — the failure is specific to the `bool` field access.

## Expected

Cross-module struct field access with a `bool` field should lower to HIR like
same-module access does; no interpreter fallback.
