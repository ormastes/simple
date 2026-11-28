# Fractional Layout Follow-Ups (Chrome 159)

> Traceability: `REQ-WEB-004` — Device baseline preservation beside `vertical-align: top|bottom`, `inline-block` `hangs_from_baseline` at `k=1`, CSS 2.2 §9.5.2 negative clearance, `<svg>` `max-width` clamp fractional suppression, and 1-device-px SVG edge AA blending at `k=4`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

## Scenarios

- **AC-1**: `vertical-align: top` on a tall `<svg>` beside text preserves device baseline offset (`device-y-offset = 2` at `k=4`).
- **AC-2**: An `inline-block` with `height: 12.5px` under a taller strut snaps to `12px` at `k=1` while `20.5px` snaps to `21px`.
- **AC-3**: A `clear: both` first child with `margin-top: 40.5px` below a `30.75px` float lands at row `1323` (`y=330, device-y-offset=3`) via negative clearance.
- **AC-4**: An `<svg>` with `width: 40.5px; max-width: 40px` renders as `40px` wide at `k=1`.
- **AC-5**: A fractional `<svg width="50" viewBox="0 0 3 1">` emits `_aa_` coverage rects and blends row `66` (`~0.625` coverage) between `#000` and `#fff` at `k=4`.
