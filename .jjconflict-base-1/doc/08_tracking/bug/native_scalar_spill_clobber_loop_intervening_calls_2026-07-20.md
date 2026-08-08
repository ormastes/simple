# Freestanding native: outer-scope scalar `val`s read back corrupted inside a `while` loop with intervening calls

- **ID:** native_scalar_spill_clobber_loop_intervening_calls_2026-07-20
- **Status:** SOURCE FIXED; fresh staged execution pending
- **Severity:** high (blocks the DrawIR titlebar gradient; general hazard for any loop consuming pre-computed scalars on the freestanding lane)
- **Found by:** GRADIENT-DRAWIR lane, 2026-07-20, real OVMF boot evidence
- **Family:** same mechanical shape as
  doc/08_tracking/bug/native_tuple_spill_clobber_across_call_2026-07-19.md,
  generalized from tuples to plain u32 scalars and from one straight-line
  intervening call to repeated calls across `while`-loop iterations.

## Symptom
In `_wm_draw_ir_window_batch` (src/lib/common/ui/window_scene_draw_ir.spl,
live boot chrome path), a per-row gradient loop pushed 27× 1px
`draw_ir_box_with_style` rows lerping `titlebar_top`→`titlebar_bottom`
(u32 `val`s computed once via `_wm_titlebar_shade(title_color, ±14)` BEFORE
the loop). On screen: 27 of 28 rows pure black; only the border row —
computed by the SAME `_wm_titlebar_shade` fn but consumed OUTSIDE the loop —
painted correctly at exactly `title_color-40` per channel.

## Discriminating evidence (rules out render-side causes)
One-shot serial probe inside the loop on row 1:
`cmd_present=1 cmd_height=1 cmd_color=4278190080` (= 0xFF000000). The
DrawIrCommand was present and well-formed; the COLOR was wrong at
generation time. Not the draw_ir_adv nil-guard skip; not `_wm_titlebar_shade`
(border row proves it correct); not the push path.

## Shape
- corrupted: u32 `val`s bound before the loop, read inside the loop body
  where each iteration makes ~10 nested calls (`_wm_titlebar_lerp` →
  6× `_wm_argb_channel` + 3× `_wm_argb_clamp_u8` + `_wm_argb_from_channels`).
- unaffected: `val` from the same producer read once with no intervening
  calls between definition and use.
- Consistent with a spill-slot lifetime defect: the scalar's slot is reused
  by intervening calls and reloaded wrong on later iterations.

## Non-fixes (tried, evidence-verified no-ops or regressions)
- Typed intermediate `val` before `.push()` (the erased-receiver workaround
  pattern from vfs_boot_init.spl): rebuild byte-identical — no-op here.
- Painting the flat box first as a fail-safe: the buggy rows DO render
  (black), painting over the fallback — actively worse. Reverted.

## Workaround direction (untried, evidence-motivated)
Recompute the shades INSIDE the loop body each iteration from the stable
`title_color` (snapshot-immediately-before-use — the same fix pattern the
tuple-spill bug used). Retry protocol: one build + one OVMF boot; expect
≥10 distinct titlebar shades in the y-strip pixel table; keep the flat
single-box fallback if any row reads black.

## Current state
`_wm_draw_ir_window_batch` restored to the single flat titlebar box (strict
no-regression, Boot A verified: 1 distinct titlebar color, 0 exceptions) with
an in-code comment recording this investigation. Fix the seed's spill-slot
handling with a minimal repro (scalar hoisted over a call-bearing loop) as
the regression test, then sweep the workaround back out.

## 2026-07-23 pure-Simple root fix

The active freestanding path is the pure-Simple Cranelift adapter, not the
hand-written native register allocator. Its `value_map` was retained while
blocks were compiled sequentially, so a use in a loop body could bind to the
value produced while compiling an earlier block instead of loading the local's
runtime stack slot. Block entry now retains only `Alloc` addresses (whose slot
is the allocation itself) and reloads all ordinary cross-block values from
their persistent slots.

One focused aggressive-Cranelift smoke case pins a pre-loop `u32` across a
call-bearing `while`. Hosted Linux/macOS/Windows inherit the shared matrix,
FreeBSD selects the same case in its scoped Cranelift pass, and the existing
cross-module fixture carries the oracle through AArch64/RV64 execution plus
ARM32/RV32/Windows-ARM64 object gates. No target-specific implementation was
added. Fresh staged execution remains pending.
