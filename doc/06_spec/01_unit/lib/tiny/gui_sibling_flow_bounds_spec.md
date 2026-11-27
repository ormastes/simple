# Tiny sibling flow bounds

Status: authored manual; executable scenarios are **UNEXECUTED**. No generator,
compiler, GUI, or native verification was run for this change, per the user's
source-review-only instruction.

Executable source: `test/01_unit/lib/tiny/gui_sibling_flow_bounds_spec.spl`.

| Scenario | Required behavior |
|---|---|
| Indexed row with widths INT32_MAX, 1, 1 | Third child stays at INT32_MAX and is clipped, never wraps negative |
| Full-scan row with identical nodes | Same coordinate result when scratch capacity is insufficient |
| Indexed column with heights INT32_MAX, 1, 1 | Child coordinates and content extent saturate consistently |
| Full-scan column with identical nodes | Same saturated coordinates and extent |
| Ordinary row and column on both routes | Sizes 3, 1, 1 retain positions 0, 3, 4 and total extent 5 |

The overflow oracle uses fixed mathematical bounds, rather than comparing two
implementations that could share the same overflow. These scenarios do not
establish rendering, performance, or cross-platform qualification.
