# Engine3D live-font compatibility cannot resolve `rt_font_load`
**Status:** OPEN (unverified 2026-09-12)

`test/01_unit/lib/gpu/engine3d/font_compat_spec.spl` passes six of seven
scenarios but the live neutral glyph scenario fails with:

```text
semantic: unknown extern function: rt_font_load
```

The failure blocks live glyph, malformed/stale material, canonical atlas, and
font-memory evidence. Fix the pure-Simple runtime/SFFI ownership path; do not
replace the live case with a synthetic batch or bitmap-only fallback.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and has no cheap repro reachable within budget; left open with an explicit unverified status line.
