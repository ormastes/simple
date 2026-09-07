# `deps fast`/`deps deep` silently ignore bare tier-rooted imports (fail-open closure)

**Filed:** 2026-09-05
**Status:** RESOLVED 2026-09-06 — fixed in `src/app/deps/scanner.spl` (pure Simple); regression spec `test/01_unit/app/deps/bare_tier_root_imports_spec.spl` (7 examples, 0 failures; sspec score 83/100)
**Severity:** High — every closure-based gate and doc built on `deps fast`/`deps deep` reports an undercounted, fail-open result

## Summary

The seed's `deps fast <entry>` (`src/compiler_rust/target/bootstrap/simple deps
fast <entry>`) follows imports rooted at `std.`, `app.`, `os.` but **silently
ignores** bare tier-rooted imports — imports whose first path segment is a tier
directory name directly under `src/lib/` (e.g. `common.`, `nogc_sync_mut.`,
`nogc_async_mut.`, `gc_async_mut.`, …) rather than `std.`/`app.`/`os.`. These are
valid Simple imports used throughout `src/` (see
`doc/07_guide/language/module_system.md` — `use std.X` and `use lib.X` both
resolve from `src/lib/`; bare tier roots such as `common.X` resolve the same
way, just without the `std.`/`lib.` prefix). The tool does not error and does
not warn; it emits a normal-looking `Direct imports: N` report with the
bare-rooted edges simply missing from the closure, so every consumer reads a
falsely small/clean closure.

## Repro

```
$ cat build/nb/fixtures/deps_root_probe.spl
use std.io.{print}
use common.ui.key_code.{KeyCode}

fn main():
    print("x")

$ cat build/nb/fixtures/deps_root_probe2.spl
use common.ui.key_code.{KeyCode}

fn main():
    pass
```

```
$ src/compiler_rust/target/bootstrap/simple deps fast build/nb/fixtures/deps_root_probe.spl
=== deps fast: build/nb/fixtures/deps_root_probe.spl ===
Direct imports: 1

  src/lib/nogc_sync_mut/io.spl  (35 transitive files)
    ... (35 files, all under the std.io closure) ...

# src/lib/common/ui/key_code.spl NEVER appears, despite the bare `use common.ui.key_code.{KeyCode}` line.

$ src/compiler_rust/target/bootstrap/simple deps fast build/nb/fixtures/deps_root_probe2.spl
=== deps fast: build/nb/fixtures/deps_root_probe2.spl ===
Direct imports: 0

# Bare-only import form: reports ZERO direct imports and ZERO src/ lines in the
# closure at all, even though `src/lib/common/ui/key_code.spl` exists on disk
# and is a real dependency.
```

Real-world instance — `src/app/ui_showcase/hosts/host_gui.spl` has 6 `use`
lines, 4 of them bare-tier-rooted:

```
use nogc_sync_mut.ui.gui_renderer.{...}
use common.ui.draw_ir_v3.{DrawIrV3Scene}
use common.ui.screen_host.{ScreenHost}
use common.ui.key_code.{...}
use common.ui.host_input_event.{...}
use app.ui_showcase.hosts.scene_raster.{raster_scene_argb}
```

```
$ src/compiler_rust/target/bootstrap/simple deps fast src/app/ui_showcase/hosts/host_gui.spl
=== deps fast: src/app/ui_showcase/hosts/host_gui.spl ===
Direct imports: 1

  src/app/ui_showcase/hosts/scene_raster.spl  (1 transitive files)
    src/app/ui_showcase/hosts/scene_raster.spl
```

Only the `app.`-rooted import is followed. All 4 bare-tier-rooted imports
(`gui_renderer.spl`, `draw_ir_v3.spl`, `screen_host.spl`, `key_code.spl`,
`host_input_event.spl`) are entirely absent from the reported closure of 2
files.

Consequence for a consumer gate, reproduced directly:

```
$ sh scripts/check/check-ui-slim-closure.shs src/app/ui_showcase/hosts/host_gui.spl \
    src/os/compositor src/os/drivers src/os/kernel src/lib/skia src/lib/gc_async_mut/gpu
PASS — 2 file(s) in closure, 0 forbidden      (rc=0)
```

This is a fail-open verdict: the gate never saw the 4 missing files and
therefore cannot know whether any of them (or their own transitive imports)
pull in a forbidden prefix.

## Affected surface

- Every direct consumer of `deps fast` / `deps deep` output (`src/app/deps/*`,
  `src/app/package.registry/index.spl`, `src/app/package/registry/index.spl`).
- `doc/07_guide/compiler/deps_tool.md:44` — states "Input: full transitive
  closure (`[text]` of resolved file paths)" for `deps deep`. This is false for
  any entry with a bare-tier-rooted import: the closure is silently partial.
- `scripts/check/check-ui-slim-closure.shs` — the NFR-UI-SLIM-002 gate
  (`doc/02_requirements/nfr/ui_slim_kernel_plugin.md`) built directly on `deps
  fast`. Hardened in this same change (see below) to fail closed instead of
  reporting a blind PASS, but the underlying resolver defect is unfixed.
- Any future or existing closure-based lint/gate that trusts `deps fast`/`deps
  deep` output as complete.

## Unblock

The pure-Simple deps resolver (candidates: `src/app/deps/scanner.spl`,
`src/app/deps/growth_band.spl`, `src/app/deps/deep_report.spl` — grep
`/usr/bin/grep -rln 'deps fast\|fn deps_' src/app src/compiler`) must resolve a
bare tier-rooted `use` path (first segment one of the tier directory names
directly under `src/lib/`, e.g. `common`, `nogc_sync_mut`, `nogc_async_mut`,
`gc_async_mut`, `gc_sync_mut`, `gc_async_immut`, `gc_sync_immut`,
`nogc_async_mut_noalloc`, …) via the same rule the module resolver already uses
for `std.X`/`lib.X` (`doc/07_guide/language/module_system.md` § Module Path
Syntax: "`use std.X` and `use lib.X` both resolve from `src/lib/`") — i.e.
`common.ui.key_code` and `std.common.ui.key_code` must resolve to the same
file, `src/lib/common/ui/key_code.spl`. **Fixed 2026-09-06 — see Resolution below.** (Original note: do not fix in this change) — this
record exists to unblock that separate fix; this change only hardens the one
gate that was relying on the broken tool.

## Evidence retained

- `build/nb/fixtures/deps_root_probe.spl`, `build/nb/fixtures/deps_root_probe2.spl`
  (untracked, left in place for re-repro).

## Which implementation produced the buggy output (checked 2026-09-06)

`deps` is **not** a Rust command. `src/compiler_rust/driver/src/main.rs:730-739`
registers it as `CommandEntry { name: "deps", app_path: "src/app/deps/main.spl",
rust_handler: Handler::Custom(...) }` whose Rust handler only prints
`error: deps app not found` — it is an absence fallback, never an
implementation. The seed therefore *interprets* `src/app/deps/main.spl`, so the
buggy output above came from the pure-Simple scanner. The record's wording "the
seed's `deps fast`" meant "deps run under the seed binary", not "a Rust deps".
No Rust mirror fix is needed.

## Resolution (2026-09-06)

Root cause — `src/app/deps/scanner.spl`, `_deps_resolve_module`:
`_deps_module_to_relpath` (was :36, now :52) aliases only `std.` -> `lib.`;
step 3 tried `src/<relpath>` (for `common.ui.key_code` that is
`src/common/ui/key_code.spl`, which does not exist), and step 4's `src/lib/<tier>/…`
search was gated on `relpath.starts_with("lib/")` (was :144). A bare tier root
therefore never had `src/lib/` prepended, `_deps_resolve_module` returned `""`,
and both `_scan_file_recursive` and `_direct_imports` skipped it under
`if resolved != ""` — silently.

Fix (three parts, all in `scanner.spl`):
1. `_deps_lib_tiers()` / `_deps_is_lib_tier()` (:40-50) — the 10-family tier
   list copied in order from `module_loader_resolve.spl`'s `fams`. The old
   step-4 list had only 5 of the 10 and is now the same constant.
2. New step **3b** (:159-171): when the first path segment is a tier directory,
   try `src/lib/<relpath>.spl` then `src/lib/<relpath>/mod.spl`. `common.ui.key_code`
   and `std.common.ui.key_code` now resolve to the same file.
3. New `_unresolved_imports(file_path) -> [text]` returning the module names of
   direct imports that resolve to nothing; `_run_fast` and `_run_normal` print
   `Unresolved imports: N` plus one `UNRESOLVED: <module>` line each. A hole in
   the closure is now reported instead of dropped.

Evidence (seed = `src/compiler_rust/target/bootstrap/simple`):

| | before | after |
|---|---|---|
| `deps fast src/app/ui_showcase/hosts/host_gui.spl` direct imports | 1 | 6 |
| same, unique `src/**.spl` in reported closure | 2 | 40 |
| `check-ui-slim-closure.shs` on host_gui | `PASS — 2 file(s), 0 forbidden` (blind) | `PASS — 40 file(s), 0 forbidden` |

Regression spec `test/01_unit/app/deps/bare_tier_root_imports_spec.spl`: 7/7
GREEN after the fix. The discriminating RED is **4 of 7** — measured by
disabling step 3b alone — namely the two bare-root resolutions, the bare-root
transitive-closure case, and "a resolvable bare tier import is NOT reported as
unresolved"; the `std.`-prefixed control and the missing-module negative are
green either way, as they should be. (The very first draft showed every example failing,
but that was confounded: `_unresolved_imports` did not exist yet and the fixture
`use` lines were written with inline `{Symbol}`, which Simple treats as string
interpolation. Both are fixed; do not read that run as resolver RED.)
Pre-existing `deps_tool_spec.spl` (17) and `deps_deep_spec.spl` (13) stay green.

Two disclosures:
- Part 1 also changes the **order** of the existing step-4 `lib/`-prefixed
  search: it was `nogc_sync_mut, nogc_async_mut, gc_async_mut,
  nogc_async_mut_noalloc, common`, and is now the canonical resolver's order
  (`nogc_async_mut` first). A `std.X` that falls through to step 4 and exists in
  more than one tier can now resolve to a different tier's file than before —
  that is the alignment with the real module resolver, but it is a behaviour
  change on entries unrelated to this bug.
- `_unresolved_imports` covers an entry's **direct** imports only.
  `_scan_file_recursive` still skips an unresolvable transitive edge silently,
  and `_run_deep` prints no unresolved line. "Reported, not dropped" is
  therefore a property of the entry's direct imports, not of the whole closure.

## Follow-up 2026-09-06 — dotted directories, and closure-wide unresolved reporting

Closure-wide reporting immediately exposed a second, larger hole:
`deps fast src/app/ui/main.spl` reported 13 unresolved direct imports including
`app.ui.tui.app`, `app.ui.web.server`, `app.ui.electron.app`, `app.ui.tauri.app`
— modules that live in DOTTED DIRECTORIES (`src/app/ui.tui/app.spl`,
`src/app/ui.web/server.spl`, …). Five further scanner defects surfaced behind it.

**Canonical rule.** The dotted-directory rule is not in the pure-Simple
`module_loader_resolve.spl` at all; it lives in the Rust module loader,
`src/compiler_rust/compiler/src/pipeline/module_loader.rs:41-50`
(`dotted_dir_from`) and `:78-130` (`resolve_parts_from_root`): walking the
non-final segments, a segment that is not a real directory may instead be
folded into the CURRENT directory's name with a `.`
(`<parent>/<basename(cur)>.<segment>`), and the final segment is then tried as
`<cur>/<last>.spl`, `<cur>/<last>/__init__.spl`, and
`<dotted dir>/__init__.spl`. Mirrored verbatim as `_deps_dotted_dir_from` /
`_deps_resolve_parts_from_root` (step 3c), which is why the spec fixture needs a
real `x/a` directory beside `x/a.b/` — exactly the `src/app/ui` + `src/app/ui.tui`
shape the repo has.

Also fixed in `scanner.spl`, each one a separate fail-open source:
- **Docstring prose read as imports.** `_use_lines_of` now tracks `"""` fences;
  `use panel_with_text_family for an explicit family."""` was being parsed as an
  import. The three duplicated line loops now share it.
- **`use lazy X`, `pub use X`, `use x.y*`** were unparsed or misparsed;
  `pub use <DotlessSymbol>` (a symbol re-export, e.g. `pub use BlockDevice`) is
  now correctly not treated as a module path.
- **`__init__.spl`** is now probed beside every `mod.spl` on every root.
- **Member imports** (`use std.js.types.js_types.JsValue` — 44 of the residual
  edges) fold ONE level to the prefix, and only when the prefix is an ordinary
  module FILE. Both guards are load-bearing: an unbounded fold walks
  `common.ui.<typo>` up to `src/lib/common.spl` and silently re-opens this bug.
- **Cross-tier fallback for a bare tier root.** `common.ui.theme_package` really
  lives at `src/lib/nogc_sync_mut/ui/theme_package.spl`; the real compiler
  accepts it (`simple compile src/app/ui.web/server.spl` reports no unresolved
  import for it, while a bogus `common.ui.zzz_no_such` does), so a bare tier root
  now falls back to the same cross-tier search `std.X`/`lib.X` already used.
- **`rt_env_get("SIMPLE_LIB")` can be nil**, which reached `last_index_of` on a
  nil receiver once the new path helpers used it; now `?? ""`.

`_run_fast`/`_run_normal` now print `Unresolved imports: N` for every hole found
ANYWHERE in the walk, each as `<module>  (imported by <file>)`, and print the
line unconditionally so `0` is stated rather than implied.

`scripts/check/check-ui-slim-closure.shs`: `find_unresolved_imports` now builds
its on-disk candidates through a new `dotted_candidates` helper carrying the same
dotted-directory forms, so a dropped `app.ui.tui.app` edge ERRORs instead of
passing blind. Selftest 8/8 (new fixture 8 replays exactly that); with the
dotted forms disabled fixture 8 returns `PASS — 1 file(s) in closure` — a blind
pass — so it is load-bearing.

Measured 2026-09-06 (seed `src/compiler_rust/target/bootstrap/simple`), forbidden
set `src/os/compositor src/os/drivers src/os/kernel src/lib/skia src/lib/gc_async_mut/gpu`:

| entry | direct | unresolved | gate verdict |
|---|---|---|---|
| `src/app/ui/main.spl` | 1 -> 20 | 0 | `FAIL — 875 file(s) in closure, 263 forbidden` (was a 2-file blind PASS) |
| `src/app/ui/backend_entry_tui.spl` | 2 | 0 | `PASS — 114 file(s) in closure, 0 forbidden` |
| `src/app/ui.tui/async_app.spl` | 14 | 0 | `PASS — 111 file(s) in closure, 0 forbidden` |

The `main.spl` FAIL is a real finding the old closure could not see, not a
regression of this change.

Spec now 10 examples, 0 failures. Discriminating RED, re-measured because step
3c's `src/lib` root subsumes step 3b: with every tier branch disabled, 4 of 10
fail; with step 3c disabled, the 2 dotted-directory examples fail. `deps_tool_spec`
(17) and `deps_deep_spec` (13) stay green.
