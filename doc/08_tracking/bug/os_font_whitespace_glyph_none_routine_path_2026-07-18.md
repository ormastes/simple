# Whitespace glyphs return `None` on the routine rasterization path

**Date:** 2026-07-18
**Status:** fixed / landed (`395a3f7b37d`)
**Severity:** P2 — spurious `None` on a routine path (whitespace) drove the
baremetal rasterizer into the Option-unwrap fault class and broke dylib-lane
parity.
**Component:** `src/lib/common/encoding/sfnt_glyf.spl` (glyf outline
rasterizer).

## Symptom

Whitespace characters (space and other zero-contour glyphs) produced `None`
from the glyf rasterizer instead of a valid empty bitmap. On the routine text
path this meant an Option that is `None` for entirely normal input (every
space), which then had to be unwrapped downstream — feeding straight into the
baremetal Option-unwrap fault class — and diverged from the dylib rasterization
lane, which returns a valid empty bitmap for the same characters.

## Root cause

A glyph with zero contours (whitespace) was treated as "no glyph" and returned
`None`, rather than as a valid glyph whose bitmap is an empty `0x0` raster. A
correctly-shaped whitespace glyph is present in the font; it simply has no
outline to fill.

## Fix

`395a3f7b37d` fix(os/font): whitespace glyphs yield valid `0x0` bitmaps
(dylib-lane parity; avoids `None` on the routine path). Zero-contour glyphs now
return a valid empty bitmap so the routine path never sees a spurious `None`.

## Affected files

- `src/lib/common/encoding/sfnt_glyf.spl`

## Related

- `baremetal_option_field_unwrap_faults_class_2026-07-18.md` — the `None` on the
  routine path was one of the inputs feeding the baremetal Option-unwrap fault
  storm; returning a valid empty bitmap removes that source.
