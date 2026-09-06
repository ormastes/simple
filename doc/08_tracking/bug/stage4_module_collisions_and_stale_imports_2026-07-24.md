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

## Fixed in a follow-up change (2026-07-24)
1. **`src/app/package.registry/` vs `src/app/package/registry/` collision** —
   both sanitized to `app.package.registry`. Confirmed via `git log` + content
   diff that `src/app/package/registry/` was a stale, much smaller stub
   (signing.spl 1081 vs 11024 bytes; trust.spl 1038 vs 14473; no
   `verify.spl` equivalent; bare data types with no real Ed25519/HMAC
   signing) — not a genuine second implementation. All 4 real consumers
   (`src/app/{search,info,publish,yank}/main.spl`) already import exclusively
   via `use app.package.registry.*`. Deleted `src/app/package/registry/`
   (backed up) and the now-empty `src/app/package/`; also fixed
   `test/01_unit/app/package_cli_spec.spl`, which had been reading the stale
   stub path and asserting on its `class`-keyword type declarations instead
   of the canonical `struct`-keyword ones. See
   `doc/08_tracking/bug/dot_dir_entry_import_fallback_collision_2026-07-24.md`,
   which also fixes the broader root cause: `_driver_resolve_entry_import_exact`
   lacked explicit rewrites for most `src/app/*.*` dot-dirs, so dotted imports
   into them (e.g. `use app.ui.web.html.{...}`) could fall through to an
   unrelated ancestor `__init__.spl` and manufacture the same class of bogus
   module-name collision even without a real duplicate directory.

## Fixed in a follow-up change (2026-07-24, same push)
- The four remaining `std.alloc.sffi` importers
  (`50.mir/mir_lowering_stmts.spl` 30 sites,
  `50.mir/_MirLoweringExpr/expr_dispatch.spl` 43 sites,
  `50.mir/_MirLoweringExpr/method_calls_literals.spl` 30 sites,
  `80.driver/driver_pipeline.spl` 1 site) got the same rewrite: import deleted,
  `rt_dict_contains(D, K)` → builtin `D.contains(K)`. All 104 receivers verified
  Dict-typed. The `MirConstValue.Str("rt_dict_contains")` codegen literal in
  method_calls_literals.spl (which emits the runtime C symbol for the builtin)
  is intentionally unchanged. `grep -rln 'std.alloc.sffi' src/` is now empty.

## Open (filed, not fixed)
1. **16 sibling files in `src/app/ffi_gen.specs/` import `std.string.{NL}`**,
   which `src/lib/string.spl` does not export (NL lives in `std.text` via
   `lib.common.text`). Latent unresolved-import errors whenever those specs are
   compiled by the self-hosted resolver.
2. **91 hyphen-vs-underscore sanitization collisions** inside
   `src/app/llm_caret/claude_full/` (e.g. `commands/autofix-pr/` vs
   `commands/autofix_pr/`): the sanitizer collapses `-`→`_`. Different bug
   class from the dot-dir collisions; needs its own pass. See
   `dot_dir_entry_import_fallback_collision_2026-07-24.md`.
