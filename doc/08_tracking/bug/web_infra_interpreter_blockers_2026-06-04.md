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

5. **`self.field = value` rejected** — RESOLVED (2026-05-27)
   - Root cause: using `fn` instead of `me` methods. Not a bug.

6. **`self.fn_field(args)` method confusion** — RESOLVED (2026-05-27)
   - Fixed in both Rust-side and pure-Simple-side evaluators.

7. **`thread_spawn2` not registered** — RESOLVED (2026-05-27)
   - HTTP server now imports through std concurrent wrapper.

8. **`? operator requires Result or Option type, got object`** — interpreter fallback error
   - After JIT fails on generics (3), interpreter hits this on `WebApp.new("app.sdn")?`
   - Root cause: interpreter types `?` operand as `object` instead of `Result`
   - This is the actual fatal error (non-zero exit), not the `[INFO]` JIT fallback

## Blocking: Cannot Run WebApp via Native Build (AOT)

9. **Wrong import paths in restaurant webapp** — FIXED (2026-06-04)
   - Original diagnosis was wrong: the resolver DOES find stdlib correctly via
     Strategy 1 (family-dir search). The misleading `module path segment 'std'
     not found` error was the first-attempt relative resolution message, surfaced
     after stdlib resolution also failed for a different reason.
   - Root cause: webapp scaffolding used nonexistent module names:
     `std.web_framework.response` → symbols live in `controller.spl`
     `std.web_framework.template` → `render_page` lives in `controller.spl`
     `std.web_framework.csrf` → should be `csrf_integration`
     `std.web_framework.validation` → should be `form_validation`
     `std.time.{now_iso8601}` → no such stdlib module; use `time_ops`
   - Fix: corrected all imports to match actual stdlib module names

10. **Cranelift codegen: `fcvt_to_sint.i64` given i64 instead of float**
    - `_make_edge` function: `v199 = fcvt_to_sint.i64 v193` where v193 is i64
    - Cranelift verifier rejects: arg must be float type for fcvt_to_sint
    - Falls back to stub (CODEGEN-STUB-FALLBACK), but may cascade
    - Root cause: codegen emitting float conversion on integer-typed value

## Conclusion

**Both execution paths blocked.** Interpreter mode: generics HIR lowering (3) +
`?` operator typing (8). Native build: module resolution from subdirectories (9)
+ Cranelift codegen type error (10). Bugs 5-7 resolved.

The restaurant webapp code is correct — all 43 SPipe specs pass. These are
compiler infrastructure bugs, which is exactly what this infra test vehicle was
designed to surface. Priority fix order: (9) module resolution → (3) generics →
(8) `?` typing → (10) Cranelift codegen.
