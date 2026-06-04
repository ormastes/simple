# Web Infra Interpreter Blockers — 2026-06-04

Discovered while running `examples/06_io/webapp/main.spl` and building the
restaurant webapp infra test vehicle.

## Fixed This Session

1. **`namespace` reserved keyword used as method name** — `router.spl:141`
   - `me namespace(prefix, routes)` renamed to `me prefix_group(prefix, routes)`
   - File: `src/lib/nogc_async_mut/web_framework/router.spl`

2. **Deprecated `import` keyword in http/url.spl** — 3 copies
   - `import common from "std/http/common"` → `use std.nogc_sync_mut.http.common`
   - Files: `src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/http/url.spl`

## Blocking: Cannot Run WebApp in Interpreter Mode

3. **`Unknown type: T`** — HIR lowering error on generic type parameters
   - JIT compilation fails, interpreter fallback also fails on generics
   - Affects: `Repository<T>`, `ActiveModel<T>`, any generic stdlib usage
   - Impact: All web_framework model/persistence code unreachable

4. **Undefined export symbols in database modules**
   - `atomic_read`, `atomic_write`, `FileLock`, `WalEntry`, `WriteAheadLog`,
     `DbMetrics`, `IndexType`, `ColumnIndex`, `IndexManager`, `FtsIndex`, etc.
   - Root cause: database module chain exports symbols that aren't defined in
     the interpreter-visible scope (likely require compiled extern dispatch)

5. **`self.field = value` rejected** (previously documented)
   - `interpreter_self_field_assign_rejected_2026-05-27.md`

6. **`self.fn_field(args)` method confusion** (previously documented)
   - `interpreter_fn_field_method_confusion_2026-05-27.md`

7. **`thread_spawn2` not registered** (previously documented)
   - `interpreter_thread_spawn2_not_registered_2026-05-27.md`

## Conclusion

Web framework requires compiled mode for end-to-end execution. Interpreter mode
blocked by generics (3), database module chain (4), and method dispatch (5-7).
The restaurant webapp structure and specs verify correct code patterns via
text-grep; live HTTP testing requires Phase 2 compiled EXE path.
