# 3px dotted border at 1x places dots differently from Chrome 159

- **Found:** 2026-11-19, while re-pinning `border_dash_layout_chrome159_spec.spl` from a 1x Chrome render (thin-dash lane).
- **Symptom:** at device scale 1, the 3px `dotted` box in that spec puts its dots at different x positions than Chrome. The earlier pins came from a dpr4 Chrome render but ran at 1x, and they matched Simple rather than Chrome, which hid the difference.
- **Coverage removed:** 46 pins for the 3px dotted case were dropped from the spec because they asserted non-Chrome values. No spec covers 3px dotted at 1x now.
- **Next:** measure Chrome's 1x dot centres for a 3px dotted edge (200px box, `--force-device-scale-factor=1`), compare them with `border_dot_row_spans` / dot-gap fitting, and re-add pins measured from Chrome.
- **Status:** open.
