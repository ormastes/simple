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

10. **Cranelift codegen: float/int type mismatches in multiple functions**
    - `fcvt_to_sint.i64` with i64 arg, `fpromote.f64` with i64 arg, return type mismatches
    - Affects: `_make_edge`, `dyn_torch_tensor_copy_values`, `ComponentStats.get_metric`,
      `_bm_shade_vertex`, `_bm_rasterize_triangle`, and several GPU/SIMD functions
    - Falls back to stub (CODEGEN-STUB-FALLBACK) — non-fatal for webapp code
    - Root cause: codegen emitting float operations on integer-typed values

11. **Native build links all of `--source src/lib` including wrong-arch code**
    - RISC-V inline assembly (csrs, csrw, mie) compiled on x86_64 → 20+ asm errors
    - Linking fails: `fatal error: too many errors emitted`
    - Root cause: `native-build --source src/lib` compiles ALL lib files including
      `nogc_async_mut_noalloc/` baremetal code, not just webapp-reachable modules
    - Binary not produced despite successful compilation of webapp files

## Conclusion

**Interpreter path blocked** by generics (3) + `?` operator (8).
**Native build:** import resolution (9) FIXED. Compilation succeeds for webapp
files. Linking blocked by wrong-arch code (11) and Cranelift codegen stubs (10).
Bugs 5-7, 9 resolved.

The restaurant webapp code is correct — all 43 SPipe specs pass. Remaining
blockers are all pre-existing compiler issues, not webapp bugs. Priority:
(11) arch-filtered linking → (10) Cranelift codegen → (3) generics → (8) `?` typing.
