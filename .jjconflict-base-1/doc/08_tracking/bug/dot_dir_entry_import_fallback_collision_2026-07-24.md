# Dot-Dir Entry-Closure Import Fallback → Bogus Module-Name Collision

**Status:** FIXED (source) 2026-07-24 — awaiting a full T3 bootstrap/deploy to
verify against the deployed self-hosted `bin/simple`, since this is a
`src/compiler` change and the effect only shows up in a rebuilt binary.
**Severity:** Blocking — broke the stage-4 full-CLI native-build.
**Affected file:** `src/compiler/80.driver/driver_source_loading.spl`
  (`_driver_resolve_entry_import_exact`)
**Path:** `bug` track.

## Symptom

Stage-4 full-CLI native-build failed with:

```
native module name collision after path sanitization: 'src/app/ui/__init__.spl'
and 'src/app/ui.web/html.spl' both map to 'app.ui.web.html'; rename one file or
directory
```

`src/app/ui/web/` does **not** exist on disk — this is not a literal dot-dir
vs. slash-dir file collision (unlike the separate `package.registry` case
below). `src/app/ui/__init__.spl` is an unrelated real package file.

## Root Cause

`src/app/ui.web/` is a dot-named directory (module prefix `app.ui.web`).
Many files import from it with dotted syntax, e.g.
`use app.ui.web.html.{generate_css}` (18 external call sites: `ui.tauri`,
`ui.vscode`, `ui.browser`, `ui.electron`, `office/gui.spl`,
`wm_compare/...`, `llm_dashboard/...`, `os/desktop/...`, etc.).

During entry-closure loading, `_driver_resolve_entry_import("app.ui.web.html", ...)`
tries `_driver_resolve_entry_import_exact` on the full path, then repeatedly
strips the trailing dotted segment on failure (this stripping exists so
`use module.function`-style imports resolve to their containing module).
`_driver_resolve_entry_import_exact` had explicit dot-dir rewrites only for
`app.ui.browser` and `app.ui.render` (added previously for the same reason) —
**no rewrite existed for `app.ui.web`**, so:

1. `app.ui.web.html` — no file at `app/ui/web/html.spl`, no rewrite matches → fails.
2. `app.ui.web` — no file at `app/ui/web.spl` or `app/ui/web/__init__.spl` → fails.
3. `app.ui` — `src/app/ui/__init__.spl` **exists** → matches!

The resolver returns `src/app/ui/__init__.spl` as the "resolution" for the
original import `app.ui.web.html`. The caller (`driver.spl`, entry-closure
walk) then pushes `SourceFile(path: "src/app/ui/__init__.spl", module_name:
"app.ui.web.html")` as an alias, since the loaded file's own derived
module_name (`app.ui.__init__`) doesn't match the requested one.

Separately, bulk directory collection (`_driver_collect_sources` walking
`--source src/app`) finds the *real* `src/app/ui.web/html.spl` and correctly
derives `module_name = "app.ui.web.html"` from its path.

Both `SourceFile`s now share `module_name = "app.ui.web.html"` with different
physical paths → `_driver_module_name_collision` fires.

This bug class affects **every** dot-named directory directly under
`src/app/` that (a) lacks an explicit rewrite entry and (b) is referenced via
a dotted `use app.X.Y...` import from outside its own directory, because
`src/app/__init__.spl` (and several intermediate package `__init__.spl`
files, e.g. `src/app/ui/__init__.spl`, `src/app/dashboard/__init__.spl`)
always exist and silently satisfy the final fallback step.

## Fix

Added explicit `_driver_resolve_rewritten_import` entries in
`_driver_resolve_entry_import_exact` for every dot-named directory under
`src/app/` (24 total, mirroring the pre-existing `app.ui.browser` /
`app.ui.render` pattern): `ui.chromium`, `ui.chromium.acid2`,
`ui.chromium.devtools`, `ui.cli`, `ui.electron`, `ui.ipc`, `ui.mcp`,
`ui.none`, `ui.standalone`, `ui.tauri`, `ui.test_api`, `ui.tui`,
`ui.tui_web`, `ui.vscode`, `ui.web`, `dashboard.render`, `dashboard.views`,
`ffi_gen.specs`, `ffi_gen.templates`, `sffi_gen.templates`, `game.breakout`,
`game.rollball`, `package.registry`. These are checked before the generic
`cmm_lsp` rewrite and the terminal `""` fallback, so a dotted import for any
of these directories resolves directly to its real file instead of falling
through to an ancestor package `__init__.spl`.

## Separate, Related Finding: `package.registry` Physical Duplicate

`src/app/package.registry/` (dot-dir, live Ed25519 signing/trust
implementation) and `src/app/package/registry/` (slash-dir) both existed and
both mapped to the same sanitized module names (`app.package.registry.*`) —
a genuine collision by the literal "dot-dir + equivalent slash-dir" definition,
independent of the resolver bug above. Diff + `git log` confirmed the
slash-dir was a stale, much smaller stub (e.g. `signing.spl` 1081 bytes vs.
11024 bytes; `trust.spl` 1038 vs. 14473 bytes; no `verify.spl` equivalent;
no real Ed25519/HMAC signing, just bare data types + hex helpers). All 4 real
consumers (`src/app/{search,info,publish,yank}/main.spl`) import via
`use app.package.registry.*` dotted syntax exclusively.

`src/app/package/registry/` was deleted (backed up first); `src/app/package/`
(now empty) was removed too. `src/app/package.registry/` remains as the sole
canonical implementation.

## Verification Done

- Wrote a Python re-implementation of `_driver_module_name_from_path` and
  scanned all of `src/app` for physical dot-dir/slash-dir path collisions:
  before the fix, 7 collisions (all `package.registry.*`); after deleting the
  stale duplicate, 0.
  91 unrelated collisions remain from a *different* bug class — hyphen vs.
  underscore directory names colliding under the sanitizer's `-`→`_`
  substitution, entirely inside `src/app/llm_caret/claude_full/` (a large
  vendored/ported CLI tree). Out of scope for this fix per the task's
  definition (dot-dir vs. slash-dir only); flagged here for a future pass.
- Traced the entry-closure resolver algorithm by hand against the exact
  reported error string and confirmed a byte-for-byte match to the
  `app.ui.web.html` / `src/app/ui/__init__.spl` pair.
- Confirmed 10+ other dot-dirs (`ui.chromium`, `ui.cli`, `ui.electron`,
  `ui.ipc`, `ui.none`, `ui.tauri`, `ui.test_api`, `ui.tui`, `ui.tui_web`,
  `dashboard.render`) have real external dotted-import references and were
  exposed to the identical failure mode before this fix.

**Outstanding:** this is a `src/compiler` change; per `.claude/rules/bootstrap.md`
it needs a T3 full bootstrap + deploy before the fix is observable in the
deployed `bin/simple`, and the stage-4 full-CLI native-build should be re-run
to confirm the collision is gone end-to-end.
