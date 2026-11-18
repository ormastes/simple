# Fractional CSS `height` is truncated at 1x (`height:10.61px` paints 10 rows, Chrome 11), 2026-11-18

Status: open. Found by the dpr4 device-px block-y lane (stage 2). That lane leaves 1x byte-identical, so it does not fix this.

## Repro (1x)

`<div style="height:10.61px;background:#d0ffd0"></div><div style="font:16px 'DejaVu Sans';background:#ffd0d0">H</div>`, body margin 0, width 60, cpu_simd. Chrome 159.0.8154.6 headless, `--force-device-scale-factor=1`.

| | spacer rows | next block top |
|---|---|---|
| Chrome | 0-10 (11) | 11 |
| Simple | 0-9 (10) | 10 |

**Cause:** `Style.height_px` is an integer, so the 0.61 is dropped before layout. The block cursor never sees it; its milli residual `cy_frac` only carries margins.

**Effect:**
- Every block after the spacer is 1 px high at 1x.
- At dpr4, the snapped-top fix (`box_device_top_record`) cannot recover the fraction either. The spacer paints rows 0-39 against Chrome's 0-41.

Fractional margins are fine. They go through `block_margin_milli` and match Chrome at 1x and, with the stage-2 fix, at dpr4.

**Fix direction:** carry a milli height for an authored length, as margins already do, and add its residual to the cursor.
