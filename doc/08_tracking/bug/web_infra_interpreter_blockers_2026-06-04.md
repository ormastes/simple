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

11. **Full-scan discovery compiles unreachable wrong-arch code** — FIXED (2026-06-04)
    - Root cause: `native-build --entry` defaulted to full-scan instead of
      entry-closure discovery. `--source src/lib` compiled ALL 2600+ stdlib
      files including RISC-V baremetal asm, GPU rasterization, torch, etc.
    - Fix: auto-enable `entry_closure` when `--entry` is provided. Added
      `--no-entry-closure` escape hatch. Bootstrap already passed
      `--entry-closure` explicitly so this is a no-op for bootstrap.
    - Result: RISC-V asm errors eliminated, Cranelift codegen stubs reduced
      from ~20 to near-zero for webapp-reachable code.

12. **Linker STB_GLOBAL binding conflicts in _stubs.s** — FIXED (2026-06-04)
    - Root cause: `generate_builtin_trampoline_asm` emitted `.weak sym` then
      `.globl sym` for ELF Weak strategy — newer clang rejects binding change.
    - Fix: split match arms; `Weak` emits only `.weak` (still externally visible
      on ELF). `StrongWithAllowMultiple` keeps `.globl` for FreeBSD.
    - Result: **native-build produces a 655KB linked ELF binary** (99 files,
      0.4s compile, 11.8s link). Runtime segfaults from 717 stubbed symbols.

## Conclusion

**Native build works!** Bugs 5-7, 9, 11, 12 all fixed. Entry-closure +
weak-only stubs produce a linked ELF binary. Runtime needs more symbol coverage.
**Interpreter path** still blocked by generics (3) + `?` operator (8).

Next priority: runtime symbol coverage → (3) generics → (8) `?` typing.
