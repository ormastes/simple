# Stage-4 module collisions and stale std imports (2026-07-24)

Found while unblocking the stage-4 full-CLI dynload build (phase-1 load_sources).

## Fixed in this change
1. `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl` imported
   `std.alloc.sffi.{rt_dict_contains}` — a stale alias of the Rust seed's bundled
   stdlib (`src/compiler_rust/lib/std/src/alloc/sffi.spl`), invisible to the
   self-hosted resolver. Import deleted; 25 call sites rewritten to the builtin
   `Dict.contains()`.
2. `src/app/ffi_gen/specs/module_gen_spec.spl` duplicated
   `src/app/ffi_gen.specs/module_gen_spec.spl` (path-sanitization collision:
   both map to `app.ffi_gen.specs.module_gen_spec`). Only delta was line 29
   `std.text.{NL}` (working) vs `std.string.{NL}` (broken — `std.string` does
   not export NL). Merged the working import into the canonical dot-dir file,
   deleted the subdir copy and its empty directory.

## Open (filed, not fixed)
1. **`src/app/package.registry/` vs `src/app/package/registry/` collision** —
   both sanitize to `app.package.registry`. 7 same-named files with hugely
   divergent sizes (signing.spl 11024 vs 1081 bytes; trust.spl 14473 vs 1038)
   plus `package.registry/verify.spl` with no counterpart: two genuinely
   different implementations needing a real merge decision, not a quick delete.
   Will break stage-4 load_sources if/when both enter the entry closure.
2. **16 sibling files in `src/app/ffi_gen.specs/` import `std.string.{NL}`**,
   which `src/lib/string.spl` does not export (NL lives in `std.text` via
   `lib.common.text`). Latent unresolved-import errors whenever those specs are
   compiled by the self-hosted resolver.
3. Four compiler files still import the seed-only `std.alloc.sffi` path
   (`50.mir/mir_lowering_stmts.spl`, `50.mir/_MirLoweringExpr/expr_dispatch.spl`,
   `50.mir/_MirLoweringExpr/method_calls_literals.spl`,
   `80.driver/driver_pipeline.spl`). They resolved in today's stage-2/3/4 runs
   (different search-path behavior than the vhdl dir), but the alias is stale;
   same `.contains()` rewrite applies if they ever fail.
