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

## Suspected mechanism

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

## Not done

No workaround was applied. The spec is NOT skipped (that needs approval) and no
assertions were deleted. Fixing this is compiler-internals work, outside the
`.spl`-only scope of the campaign that found it.

Found by: unified 2D event/panel campaign, Wave A.
Plan: `doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md`
