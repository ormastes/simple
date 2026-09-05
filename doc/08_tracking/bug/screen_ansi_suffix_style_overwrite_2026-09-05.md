# screen_ansi_spec: 2 pre-existing RED examples hidden by a parse error since 2026-08-27

**Date:** 2026-09-05 · **Status:** OPEN · **Lane:** ui_slim_kernel_plugin (found while landing A03)

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

## Unblock

Fix the splice logic in `src/app/ui.tui/screen.spl` (`_splice_row`, extracted verbatim
from `put_text` on 2026-09-05) so a partial overwrite inside a styled block keeps the
suffix style and the overwritten glyph. Ship the fix with this spec green plus a
generalization example for a 3-block row. Do not weaken the two examples.
