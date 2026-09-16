# Engine3D live-font compatibility cannot resolve `rt_font_load`

`test/01_unit/lib/gpu/engine3d/font_compat_spec.spl` passes six of seven
scenarios but the live neutral glyph scenario fails with:

```text
semantic: unknown extern function: rt_font_load
```

The failure blocks live glyph, malformed/stale material, canonical atlas, and
font-memory evidence. Fix the pure-Simple runtime/SFFI ownership path; do not
replace the live case with a synthetic batch or bitmap-only fallback.
