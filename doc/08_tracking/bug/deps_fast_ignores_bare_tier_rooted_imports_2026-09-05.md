# `deps fast`/`deps deep` silently ignore bare tier-rooted imports (fail-open closure)

**Filed:** 2026-09-05
**Status:** OPEN — repro confirmed, resolver NOT fixed (out of scope for this record's author)
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
file, `src/lib/common/ui/key_code.spl`. **Do not fix in this change** — this
record exists to unblock that separate fix; this change only hardens the one
gate that was relying on the broken tool.

## Evidence retained

- `build/nb/fixtures/deps_root_probe.spl`, `build/nb/fixtures/deps_root_probe2.spl`
  (untracked, left in place for re-repro).
