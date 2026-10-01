# Stage-4 module collisions and stale std imports (2026-07-24)

Found while unblocking the stage-4 full-CLI dynload build (phase-1 load_sources).

## Recurrence during Target 5/6 self-hosting (2026-09-29)

The older pure-Simple Stage4 standalone compiler again refused two stale
literal path pairs while AOT compiling the current compiler entry. The
`src/app/package/registry/` stub copy had reappeared beside the canonical
`src/app/package.registry/` implementation. The seven stub files were removed;
the package CLI source spec now reads the canonical `struct` definitions, and
the search example names its real config path and registry value. A no-stub
native package CLI spec passed 3 examples with zero failures.

The next load reported the reintroduced
`src/app/ffi_gen/specs/module_gen_spec.spl` copy beside the canonical
`src/app/ffi_gen.specs/module_gen_spec.spl`. The sole working delta,
`use std.text.{NL}`, was retained in the canonical file and the duplicate
deleted. A literal `src/**/*.spl` path-to-module scan now finds zero such
duplicate groups.

The third bounded AOT attempt stopped on a different collision:
`src/lib/gc_sync_mut/src/tooling/regex_nfa.spl` and
`src/lib/gc_async_mut/src/tooling/regex_nfa.spl` both became
`tooling.regex_nfa` in that older tool's flat source loader. These are
distinct GC-family facades, not the stale dot-directory copies above. They
must keep their family namespace or be excluded by a correct reached-source
closure; deleting either to satisfy the old loader would change the language
surface. No current-source Stage4 executable was produced by these attempts.
Logs are under `build/target56-current-stage4/` in the isolated Target 6
worktree.

A follow-up tried the older Stage4 binary with
`SIMPLE_NATIVE_BUILD_ENTRY=src/compiler/80.driver/main.spl`. The reached-source
walk avoided the GC-family collision and loaded 822 source files, but phase 2
reported 124 parse errors. Its flat AST bridge rejects current declaration
nodes (for example, `pub use` in `driver_public_api.spl`); the run peaked at
14,995,032 KiB RSS and produced no compiler. Pre-setting
`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` skipped that walk and loaded only the
entry file, which failed on missing imported module surfaces. These are
limits of the older standalone binary, not evidence against the current
source loader. Logs are under `build/target56-entry-walk/` and
`build/target56-entry-closure/` in the isolated worktree.

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
1. **Resolved 2026-09-29:** the 12 remaining sibling files in
   `src/app/ffi_gen.specs/` imported `std.string.{NL}`, which
   `src/lib/string.spl` does not export. They now import `std.text.{NL}` via
   `lib.common.text`, matching the canonical `module_gen_spec.spl`.
2. **91 hyphen-vs-underscore sanitization collisions** inside
   `src/app/llm_caret/claude_full/` (e.g. `commands/autofix-pr/` vs
   `commands/autofix_pr/`): the sanitizer collapses `-`→`_`. Different bug
   class from the dot-dir collisions; needs its own pass. See
   `dot_dir_entry_import_fallback_collision_2026-07-24.md`.
