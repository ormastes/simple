# `env_get(...) ?? default` is a DEAD fallback against `std.io_runtime`'s `env_get` — silently yields `""` instead of the default

- **ID:** env_get_nil_coalesce_dead_fallback_2026-07-25
- **Status:** OPEN — root-caused, one instance fixed, general sweep NOT done
- **Severity:** high — silent wrong value, no error, no warning; the idiom reads
  as correct and is used ~680 times in-tree.

## The defect

`env_get` exists with **two different return types**:

| definition | returns |
|---|---|
| `src/lib/nogc_sync_mut/io_runtime.spl:174` (`std.io_runtime`) | **`text`** |
| `src/lib/nogc_sync_mut/env/variables.spl:11` | **`text`** |
| `src/lib/nogc_sync_mut/src/config.spl:764` | **`text?`** |

`??` (nil-coalesce) only fires on `nil`. A plain `text` is never `nil` — an unset
variable comes back as `""`. So against the first two definitions:

```
val x = env_get("UNSET_VAR") ?? "fallback"      # x == ""   NOT "fallback"
```

Verified by probe on the session-built full CLI:

```
is nil?      : false
?? fallback  : []          <-- empty, fallback never taken
```

The idiom looks correct because a **sibling `env_get` really does** return
`text?`, where `??` is the right thing. Which one you get depends on your import.

## How it surfaced

`widget × host-WM` showcase cell reported `status=fail reason=ppm-write-failed`
with the default path, but passed when `SIMPLE_WM_HEADLESS_CAPTURE_PPM` was set.
The write was never the problem:

```
wm_widget_showcase_host_headless_failed_ppm_path=          <-- EMPTY
wm_widget_showcase_host_headless_failed_ppm_bytes=1663215  <-- payload fine
```

`ppm_path` was `""`, because
`env_get("SIMPLE_WM_HEADLESS_CAPTURE_PPM") ?? path_join(...)` never reached the
`path_join`. Hours went into ruling out permissions, directory existence, payload
size, filename collisions and `path_join` correctness — all of which were fine —
because the failure was reported as a *write* failure and the path was not
printed. (That diagnostic gap is now fixed; see "Fixed" below.)

## Fixed

- `examples/06_io/ui/wm_widget_showcase_gui.spl` — the `ppm_path` site now uses
  an explicit `!= ""` check instead of `??`, with a comment explaining why.
- Same file: the failure branch now prints `failed_ppm_path` /
  `failed_ppm_bytes`, and `dir_create_all`'s ignored return is checked and
  reported as a distinct `tmp-root-create-failed` reason. Without these two the
  root cause stays invisible.

## NOT fixed — the general case

`grep -rn 'env_get([^)]*) *??' --include=*.spl src examples` → **680 occurrences.**

**That is 680 occurrences, not 680 bugs.** A site is only broken if the
`env_get` in scope is a `text`-returning one. Sites importing the `text?`
variant are correct. Each occurrence must be checked against its own import
before being touched — a blind sweep would be wrong.

Highest-count files (import not yet verified per-file):

| count | file |
|---|---|
| 22 | `examples/06_io/ui/widget_showcase_gui.spl` |
| 17 | `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` |
| 14 | `src/app/io/_CliCompile/compile_targets.spl` |
| 9 | `examples/06_io/ui/wm_web_standards_showcase_gui.spl` |
| 9 | `examples/06_io/ui/wm_graphics_2d_showcase_gui.spl` |
| 9 | `examples/06_io/ui/graphics_2d_showcase_gui.spl` |
| 8 | `examples/06_io/ui/wm_widget_showcase_gui.spl` (1 of 8 fixed) |
| 8 | `src/app/ui.web/server.spl` |

Note the two other host-WM showcase wrappers (2D, web) each carry 9 — the cells
I have not yet run. Expect the same class of failure there.

## Recommended real fix (pick one, do it deliberately)

1. **Unify `env_get` on `text?`** and let `??` mean what every call site already
   assumes. Most correct; touches every `text`-returning call site.
2. **Rename** so the two cannot be confused (`env_get` -> `text?`,
   `env_get_or_empty` -> `text`). Makes the wrong idiom impossible to write by
   accident.
3. At minimum, make the compiler **warn on `??` applied to a non-optional**
   expression — it is provably dead code and would have caught all 680 sites,
   plus the four other same-name-collision defects found the same day.

Option 3 is the same lever as "make same-name collisions loud at registration"
(`doc/03_plan/ui/showcase_matrix_replan_2026-07-25.md` P5): a diagnostic that
turns a silent whole class into a build-time error.

## Related — fifth same-name divergence found 2026-07-25

`ant-trace`/`ant_trace`, `CompiledSymbolKind`, `Engine2D` across tiers,
`MouseEvent` (ps2_mouse vs input_event), and now `env_get` (`text` vs `text?`).
Same root habit: one name, several definitions, silently diverged.
