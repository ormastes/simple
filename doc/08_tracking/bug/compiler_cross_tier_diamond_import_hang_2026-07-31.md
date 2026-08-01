# Compiler hangs on cross-tier diamond import + call (2026-07-31)

**Status:** OPEN — compiler defect, no workaround applied.
**Impact:** `test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl` can never
run. It has never produced a `Results:` line. Any spec combining these two
imports with a real call is equally unrunnable.

## Symptom

Compilation never terminates. The log stops at **exactly 1,938 lines** (a flood
of `[gc-warning] Higher-layer module ... imported in restricted context`) and
then prints `Process timed out`. **Zero examples execute.**

Not a slow compile: the line count is byte-identical at the default runner limit
AND at `SIMPLE_TIMEOUT_SECONDS=2000` (~33 min). A 6x larger budget produces the
same stopping point, so it is stuck, not progressing. The env var is definitely
honoured — it turned a different spec from timeout into 3/3.

## Minimal reproducer (9 lines)

```simple
use std.spec.*
use common.ui.widget_draw_ir.{widget_tree_to_draw_ir_with_theme}
use nogc_sync_mut.ui.theme_package.{theme_package_render_snapshot}

describe "repro: unused widget_draw_ir import + theme_package call":
    it "calls theme_package_render_snapshot":
        val snapshot = theme_package_render_snapshot("aetheric_dark")
        assert_true(snapshot.id != "")
```

## Controls (both pass — this is what makes it a real finding)

| Case | Result |
|---|---|
| Both imports **+ the call** | HANGS, `Process timed out`, exactly 1938 lines |
| The call, but **no** `widget_draw_ir` import | `Results: 1 total, 1 passed, 0 failed` |
| Both imports, **no** call (`assert_true(true)`) | `Results: 1 total, 1 passed, 0 failed` |

**Both conditions are required.** `widget_draw_ir` is imported and NEVER USED —
its mere presence in the import list is half the trigger. Removing either the
unused import or the call makes it pass in ~1 s, every time.

Reproducer and both controls are preserved at
`scratchpad/lane_backup/compiler_bug_repro/` (`zzv_repro_spec.spl`,
`zzv_ctrl_noimport_spec.spl`, `zzv_ctrl_nocall_spec.spl`). They are deliberately
NOT left under `test/` — the reproducer would hang the whole suite.

## Suspected mechanism (PARTLY SUPERSEDED — see "Static analysis 2026-08-01")

A genuine cross-tier diamond in one compilation unit:
- `common.ui.widget_draw_ir` (common tier) reaches UP into
  `std.nogc_sync_mut.text_layout.font_renderer` (nogc_sync_mut tier)
- `nogc_sync_mut.ui.theme_package` reaches back DOWN into
  `common.ui.theme_render_snapshot` (common tier)

With both edges present and a real call forcing full return-type resolution, the
module/type resolver appears to cycle or blow up. The 1,938 gc-warnings about
higher-layer imports in restricted contexts are the visible surface of the same
tier inversion.

## Two failure signatures that MUST NOT be conflated

Conflating these burned most of one lane's budget:
- **Type A — `ERROR: test daemon timed out`, ~1885 lines.** A COLD-COMPILE
  artifact. Self-resolves on retry once the daemon's module cache warms. Several
  bisection steps looked guilty under Type A and passed on retest.
- **Type B — `Process timed out`, exactly 1938 lines.** The real deterministic
  hang. Non-resolving across repeated reruns with a warm daemon.

Always retry once before believing a hang.

## Static analysis 2026-08-01 (read-only; hang NOT re-run)

Box was in an ENOSPC/high-load state, so this pass is source reasoning only — no
build, no rerun. Everything below is file:line-checked against current source.

### Which engine is hanging — pinned to the Rust seed

The exact string `[gc-warning] {label} module '...' imported in restricted
context (...)` exists in ONE place:
`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:196-200`
(emitted at `:225`). The pure-Simple checker
(`src/compiler/35.semantics/gc_boundary_check.spl:246`) uses a different wording
(`error[...]: runtime family '...' imports higher-layer family '...'`). So the
1,938-line log is unambiguously the **Rust seed interpreter's module loader**,
not the pure-Simple compiler. (Consistent with `simple test` delegating to a seed
child.) The `SIMPLE_LAZY_PARSE` lazy loader
(`src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl:19-21`) is
default-OFF and is **not** on this path; the seed loads `use lazy` eagerly
(`.../module_evaluator/evaluation_helpers.rs:580-584`).

### (a) The claimed diamond exists — but its stated link to the warnings is WRONG

Both edges are real:
- `src/lib/common/ui/widget_draw_ir.spl:45` → `std.nogc_sync_mut.text_layout.font_renderer` (common → nogc_sync_mut, UP)
- `src/lib/nogc_sync_mut/ui/theme_package.spl:10` → `common.ui.theme_render_snapshot` (nogc_sync_mut → common, DOWN)

But **neither edge can produce a gc-warning.**
`gc_boundary_warning_message()` returns `None` as soon as *either* endpoint is
the `common` family (`module_loader.rs:180-185`), and family is derived purely
from the path component after `lib/`/`std/` (`:134-147`). Both edges have a
`common` endpoint. A static walk of the 64-module import closure reachable from
the two reproducer imports found **zero** warning-producing edges.

⇒ The doc's line *"the 1,938 gc-warnings ... are the visible surface of the same
tier inversion"* is **false**. The flood comes from somewhere else in the
closure. **This is the biggest remaining unknown** (see Open below).

### A real cycle does exist — and it is entirely INSIDE the common tier

Only one SCC (size 3) in the reachable closure:
- `src/lib/common/ui/style.spl:8` → `common.ui.theme_registry`
- `src/lib/common/ui/theme_registry.spl:28` → `common.ui.style`
- `src/lib/common/ui/theme_registry.spl:29` → `common.ui.glass.tokens`
- `src/lib/common/ui/glass/tokens.spl:627` → `common.ui.theme_registry`  ← back-edge, a **mid-file** `use` at line 627

`theme_registry.spl` exists *specifically to break* core→platform cycles (see its
header, `:5-13`); `glass/tokens.spl:627` re-introduces one. Its singleton is a
module-level `var` (`theme_registry.spl:92 var _theme_registry_singleton: [ThemeRegistry] = []`,
getter `:98`) with **explicit**, non-idiomatic registration
(`glass/tokens.spl:628 fn _register_glass_tokens()`; header comment: *"No
module-init idiom exists in Simple; registration is explicit"*). That is exactly
the known repo-wide "module-level val/var undefined by ORDER" hazard.

### (c) The tier boundary is INCIDENTAL, not essential

The only cycle is `common`-internal. The cross-tier edges are ordinary DAG edges
that merely change **which SCC member is entered first**. Predicted consequence:
the reproducer would still hang with two same-tier imports that reorder entry
into the style/theme_registry/glass.tokens SCC the same way. Renaming the bug
around "cross-tier" is misleading; the load-ORDER change is the trigger. An
unused import is load-bearing precisely because `use` is eager in the seed, so it
still reorders the graph walk.

### (d) Memoisation exists; it is not missing, it is order-sensitive

All loader state is `thread_local` in `src/compiler_rust/compiler/src/module_cache.rs:57-74`
(`MODULE_EXPORTS_CACHE`, `MODULES_LOADING`, `MODULE_LOAD_DEPTH`,
`PARTIAL_MODULE_EXPORTS_CACHE`, `TOTAL_MODULES_LOADED`). In `module_loader.rs`:
- `:737` cache hit → returns cached exports
- `:762-773` in-progress hit → returns **partial** exports, else a silent **empty dict**
- `:554-560` `MAX_MODULE_DEPTH` guard, `:778-789` module-count guard

So the visited-set covers this shape; what it does *not* do is give a
deterministic answer — `:773`'s empty-dict fallback means whichever SCC member is
entered first gets real exports and the others get `{}`. That is the order
sensitivity the reproducer exposes.

### (b) Classification — what it is NOT, and the open discriminator

- **Unbounded recursion: RULED OUT.** `module_loader.rs:554-560` and `:778-789`
  convert runaway import depth/count into a `CompileError`, not a hang.
- **Infinite loop in the theme path: unlikely.** `grep -c "while "` is **0** in
  all of `simple_theme.spl`, `style.spl`, `theme_registry.spl`,
  `glass/tokens.spl`. No spin site found on the `theme_package_render_snapshot`
  → `SimpleTheme.from_css` path.
- **Live candidate — blocked write on a full stderr pipe.** `module_loader.rs:225`
  is a bare, **undeduplicated** `eprintln!`, and it is emitted at `:730`
  **BEFORE** the cache check at `:737`. Every *repeat visit* of the same edge
  re-fires it. A child that fills the runner's stderr pipe blocks in `write()`
  forever. This fits the doc's own strongest evidence — a **byte-identical stop
  at 1,938 lines under a 6× timeout budget** — at least as well as a compute
  loop, and better explains a stop at a fixed *output* quantity.

**Honest status: not decided between "blocked-on-output deadlock" and "compute
spin further down".** The two have different fixes, so do not pick one yet.

**Decisive experiment (no rebuild, no repo write):** rerun the reproducer with
`SIMPLE_NO_DEPRECATED_WARNINGS=1`, which suppresses the `eprintln!` outright at
`module_loader.rs:222-224`.
- Hang disappears → it is the output path (blocked pipe), fix = (1) below.
- Hang persists with no output → it is compute or a lock; then take per-thread
  `utime` deltas from `/proc/<pid>/task/*/stat` to split spinning (utime climbs)
  from blocked (utime flat).

### (e) Proposed change — NOT APPLIED

1. **Dedup and reorder the warning** (`module_loader.rs`): move the
   `emit_gc_boundary_warning` call at `:730` to *after* the cache-hit return at
   `:737-756`, and key emission on a thread-local `HashSet<(importer, imported)>`
   so each edge warns once. Independently correct regardless of root cause, and
   removes the flood that is either the cause or the noise hiding it.
2. **Break the intra-common SCC**: move `_register_glass_tokens()` and the
   mid-file `use` at `glass/tokens.spl:627` into a separate registration module
   (e.g. `common/ui/glass/tokens_register.spl`) so `tokens.spl` no longer imports
   `theme_registry`. Removes the only cycle in the closure and the order
   sensitivity with it.
3. **Make the cycle-breaker attributable**: `module_loader.rs:770-773` silently
   returns `{}` on a cycle with no partial exports, converting a real cycle into
   missing symbols far downstream. It should record the offending edge (and
   ideally hard-error under a strict flag) so this class is diagnosable.
4. Only after the discriminator above: if the hang survives (1), hunt the compute
   spin — do **not** apply (1) and declare victory without rerunning.

### Open / unfinished

- **Where do the 1,938 warnings actually come from?** The static walk resolved
  only 64 modules; `std.skia.*`, `std.io_runtime` and other non-tier-rooted paths
  did not resolve in the scan, so the warning-producing edges are almost
  certainly in that unresolved remainder (reached via
  `nogc_sync_mut/text_layout/font_renderer.spl:102-106`). Not established.
- Whether the seed or a spawned daemon thread owns the blocked write — untested.
- Nothing was rerun; every "predicted" statement above is a prediction.

## Not done

No workaround was applied. The spec is NOT skipped (that needs approval) and no
assertions were deleted. Fixing this is compiler-internals work, outside the
`.spl`-only scope of the campaign that found it.

Found by: unified 2D event/panel campaign, Wave A.
Plan: `doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md`
