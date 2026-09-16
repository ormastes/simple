# screen_ansi_spec: 2 pre-existing RED examples hidden by a parse error since 2026-08-27

**Date:** 2026-09-05 · **Status:** FIXED 2026-09-06 (see Fix section; one spec off-by-one remains) · **Lane:** ui_slim_kernel_plugin (found while landing A03)

## What was hidden

`test/01_unit/app/ui/screen_ansi_spec.spl` — the dedicated regression suite for the
`put_text`/`put_styled` ANSI splice logic in `src/app/ui.tui/screen.spl` — had not
executed since commit `e274cd33719` (2026-08-27, header modernization). That commit
deleted the spec's helper functions (`_to_chars`, `style_at_col`, `char_at_col`, …)
and the opening `"""` of the injected docstring, so the seed reported
`parse: Unexpected token: expected pointcut expression 'pc{...}'` and every runner
counted the file as a load failure, not as 20 examples. Nothing checked splice
behaviour for nine days.

## Repair (this record's commit)

Helpers restored from `e274cd33719~1`; stray docstring fragment turned into `#`
comments. Spec now runs: `SPEC FILE VERDICT ... executed=20 passed=18 failed=2`.

## The two RED examples (pre-existing defect, NOT caused by the A03 batching change)

| line | example | observed |
|---|---|---|
| `screen_ansi_spec.spl:226` | `suffix keeps BOLD, overwritten char does not` | `expected D to equal C` — the overwritten cell shows the wrong character |
| `screen_ansi_spec.spl:322` | `two successive overwrites on same row produce correct styles` | style escape mismatch at a column after the second overwrite |

A/B in the same tree and binary (seed `src/compiler_rust/target/bootstrap/simple`,
22,744,272 B, 2026-09-05 12:35): with `screen.spl` at its pre-batching blob
`9720ee6b` → 18/20 with the same two failures; with the batched blob `2d6d19f4` →
18/20, identical. The defect is in the pre-existing `_splice_row`/`put_text` path
(styled-block partial overwrite and repeated overwrite on one row), not in `draw_hline`.

## Legacy mirror

`test/unit/app/ui/screen_ansi_spec.spl` differs from both the broken and the repaired
`01_unit` file (pre-existing, baselined divergence). It was NOT repaired; `test/unit/`
is the frozen legacy mirror excluded from directory discovery.

## Unblock

Fix the splice logic in `src/app/ui.tui/screen.spl` (`_splice_row`, extracted verbatim
from `put_text` on 2026-09-05) so a partial overwrite inside a styled block keeps the
suffix style and the overwritten glyph. Ship the fix with this spec green plus a
generalization example for a 3-block row. Do not weaken the two examples.

## Fix (2026-09-06) — Status: FIXED (one spec off-by-one remains, see below)

**Root cause** — `src/app/ui.tui/screen.spl:271` (pre-fix):

```
val gap = if prefix_active != "" and (lost_reset or prefix_active != style_entering_suffix): RESET else: ""
```

Wrong invariant: *"content may inherit the prefix's active style when the
overwritten range neither lost a RESET nor changed the style."* A write landing
wholly inside one uniform styled block satisfies that condition, so no RESET was
emitted and the new glyphs silently inherited BOLD/CYAN. The paired restore at
`:276` had the mirror defect — it only re-emitted a style when
`style_entering_suffix != ""`, so a suffix whose old style was *empty* got no
RESET when the content left a style active.

**Correct invariant, now implemented in `_splice_row` (the single owner):**
new content never inherits `prefix_active` — a RESET is emitted before any
non-empty content whenever a style is active at the end of the prefix (an SGR the
content carries, e.g. `36`, sets a colour but does not clear an inherited `1`).
The suffix restore then compares the style the emitted content *leaves in effect*
(`after_style`) against the style the first suffix token inherited in the old line,
emitting `style_entering_suffix`, or RESET when that is empty. `lost_reset` is gone.

**Evidence** (`Screen.new(10,1)`, `put_styled(0,0,"ABCDE",BOLD)` then `put_text(0,2,"X")`):

| | line |
|---|---|
| before | `ESC[1mABX ESC[1mDE ESC[0m     ESC[0m` — X is BOLD |
| after  | `ESC[1mAB ESC[0mX ESC[1mDE ESC[0m     ESC[0m` — X plain, run resumes |

**Counts** (seed `src/compiler_rust/target/bootstrap/simple`, one tree, one binary):

| spec | before (HEAD screen.spl) | after |
|---|---|---|
| `screen_ansi_spec` | 23 executed, 19 passed, 4 failed | 23 executed, **22 passed, 1 failed** |
| `screen_batching_spec` | 11/11 | 11/11 |
| `tui_theme_spec` | 39/44 | 39/44 (identical) |
| `widget_menu_tooltip_spec` | 32/33 | 32/33 (identical) |
| `windows_compat_spec` | 32/34 | 32/34 (identical) |
| `backend_matrix_spec` | 2/3 | 2/3 (identical) |
| `dependency_closure_gate_spec` | 7/9 | 7/9 (identical) |
| `terminal_size_numeric_guard_spec` | 1/1 | 1/1 |

**Specs shipped** (`test/01_unit/app/ui/screen_ansi_spec.spl`):
reproducing — `overwrite inside a BOLD run is unstyled and the run resumes after it`;
generalization — `three-block row survives an overwrite across two style boundaries`
(BOLD | CYAN | plain, one write crossing both boundaries) and
`three successive overwrites on one row keep every block's style`.
The pre-existing `two successive overwrites on same row produce correct styles`
(`:322`) is now GREEN. Sabotage: reverting only this hunk turns all three style
examples RED again with the original messages.

## Still RED — a spec off-by-one, NOT a code defect

`screen_ansi_spec.spl:226` `suffix keeps BOLD, overwritten char does not` fails on
`expect char_at_col(line, 3) to_equal("C")`. `put_text` OVERWRITES: `X` at col 2
replaces `C`, so col 3 holds `D`. The literal has been wrong since the example was
authored (identical at `e274cd33719~1` and in the legacy mirror
`test/unit/app/ui/screen_ansi_spec.spl`), and the sibling example at `:200` uses the
same overwrite semantics correctly. Every other assertion in the example now holds
(col 0 BOLD, col 2 `X` unstyled, cols 3-4 BOLD) — the new reproducing example above is
byte-identical except for the `"D"`, and it is green. Line 25 of this record was also
a misreading: `expected D to equal C` is that char assertion, not evidence of a wrong
glyph; the runner surfaces one message per example, which masked the real style defect.
Fixing the literal was left to the owner of the original example.

**2026-09-06 addendum:** the `:226` literal was corrected to `"D"` by the lane owner (overwrite semantics); the spec is now 23/23 on the seed lane. Status: CLOSED.
